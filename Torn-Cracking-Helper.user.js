// ==UserScript==
// @name         Torn Cracking Helper
// @namespace    nodelore.torn.crack-helper.floating
// @version      1.0.0
// @description  Embedded Cracking Helper with global dictionary selector and manually saved incorrect guesses
// @author       nodelore[2786679] NEvaldas[352097]
// @match        https://www.torn.com/page.php*
// @match        https://www.torn.com/loader.php*
// @run-at       document-start
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      raw.githubusercontent.com
// @license      MIT
// ==/UserScript==

(function () {
  'use strict';

  const VERSION = '1.0.0';
  const INSTANCE_KEY = '__TCH_EMBEDDED_V100__';

  if (window[INSTANCE_KEY]) return;
  window[INSTANCE_KEY] = true;

  const DATABASES = {
    '1m': 'https://raw.githubusercontent.com/ignis-sec/Pwdb-Public/master/wordlists/ignis-1M.txt',
    '100k': 'https://raw.githubusercontent.com/ignis-sec/Pwdb-Public/master/wordlists/ignis-100K.txt',
    '10k': 'https://raw.githubusercontent.com/ignis-sec/Pwdb-Public/master/wordlists/ignis-10K.txt',
    '1k': 'https://raw.githubusercontent.com/ignis-sec/Pwdb-Public/master/wordlists/ignis-1K.txt'
  };

  const SOURCE_KEY = 'CRACKER_STATUS';
  const STORAGE_KEY = 'TCH_MANUAL_EXCLUSIONS_V160';
  const MAX_CANDIDATES = 10;

  const ITEM_SELECTOR = '.virtual-item';
  const LIST_SELECTOR = '[class*="virtualList"]';

  let source = '100k';

  try {
    source = localStorage.getItem(SOURCE_KEY) ||
      (window.innerWidth <= 768 ? '100k' : '1m');
  } catch (_) {}

  if (!DATABASES[source]) source = '100k';

  let byLength = new Map();
  let wordCount = 0;
  let loadState = 'Waiting';
  let requestId = 0;

  let allTargets = [];
  let hasServerList = false;
  let waitingForTargets = true;

  let selectedTarget = 0;
  let selectedTargetId = null;
  let selectedCandidate = 0;
  let selectedCard = null;

  let panel = null;
  let collapsed = true;

  let toolbar = null;
  let toolbarSelect = null;
  let toolbarStatus = null;
  let toolbarHost = null;

  let refreshTimer = null;
  let lastSignature = '';

  let saved = {};
  const exclusions = new Map();

  const rowState = new WeakMap();
  const listState = new WeakMap();

  let activeVirtualList = null;
  let layoutFrame = null;
  let applyingLayout = false;

  let lastPageLocation = '';
  let initialized = false;

  try {
    const parsed = JSON.parse(
      localStorage.getItem(STORAGE_KEY) || '{}'
    );

    if (
      parsed &&
      typeof parsed === 'object' &&
      !Array.isArray(parsed)
    ) {
      saved = parsed;
    }
  } catch (_) {}

  // ============================================
  // General helpers
  // ============================================

  function keyOf(id) {
    return String(id);
  }

  function isCracking() {
    const hash = location.hash.replace(/^#/, '');

    return /(?:^|\/)cracking(?:\/|$|\?)/i.test(hash);
  }

  function el(tag, className = '', value) {
    const element = document.createElement(tag);

    if (className) element.className = className;

    if (value !== undefined) {
      element.textContent = String(value);
    }

    return element;
  }

  function emptyRow(length) {
    return '.'.repeat(length);
  }

  function normaliseCharacter(value) {
    const matches = String(value || '')
      .toLowerCase()
      .replace(/ø/g, '0')
      .match(/[a-z0-9]/g);

    return matches
      ? matches[matches.length - 1]
      : '.';
  }

  function normaliseRow(row, length) {
    const text = String(row || '').toLowerCase();
    let result = '';

    for (let i = 0; i < length; i++) {
      const character = text[i] || '.';

      result += /^[a-z0-9]$/.test(character)
        ? character
        : '.';
    }

    return result;
  }

  function fingerprint(target) {
    return JSON.stringify([
      target?.ID,
      target?.password?.length ?? null,
      target?.difficulty ?? null,
      target?.type ?? null,
      target?.name ?? null
    ]);
  }

  function patternFromTarget(target) {
    if (!Array.isArray(target?.password)) return '';

    return target.password.map(slot => {
      const character = String(
        slot?.char ?? ''
      ).trim().toLowerCase();

      if (/^[a-z0-9]$/.test(character)) {
        return character;
      }

      return character === 'ø' ? '0' : '.';
    }).join('');
  }

  function readPattern(card) {
    if (!card) return '';

    return Array.from(
      card.querySelectorAll('div[class*="charSlot"]')
    )
      .filter(slot =>
        !/charSlotDummy|inactive|disabled|placeholder/i
          .test(String(slot.className))
      )
      .map(slot => {
        const label = slot.getAttribute('aria-label') || '';

        const match = label.match(
          /^([a-z0-9]),\s*Slot\s+\d+/i
        );

        if (match) {
          return match[1].toLowerCase();
        }

        const character = (
          slot.textContent || ''
        ).trim().toLowerCase();

        if (/^[a-z0-9]$/.test(character)) {
          return character;
        }

        return character === 'ø' ? '0' : '.';
      })
      .join('');
  }

  function readTargets() {
    if (hasServerList) return allTargets;

    return Array.from(
      document.querySelectorAll('.crime-option')
    ).map((card, index) => ({
      id: 'temporary-' + index,
      pattern: readPattern(card),
      fingerprint: null,
      temporary: true
    }));
  }

  // ============================================
  // Virtualised card identification
  // ============================================

  function getCardIndex(card) {
    if (!card) return -1;

    const virtualItem = card.closest(ITEM_SELECTOR);

    if (virtualItem) {
      const list = virtualItem.closest(LIST_SELECTOR);

      if (list) {
        const items = Array.from(
          list.children
        ).filter(item =>
          item.matches(ITEM_SELECTOR)
        );

        const directIndex = items.indexOf(virtualItem);

        if (directIndex >= 0) {
          const baseY = getTranslateY(
            virtualItem.style.transform
          );

          const estimatedIndex =
            Math.round(baseY / 51);

          if (
            estimatedIndex >= 0 &&
            estimatedIndex < allTargets.length
          ) {
            return estimatedIndex;
          }

          return directIndex;
        }
      }
    }

    return Array.from(
      document.querySelectorAll('.crime-option')
    ).indexOf(card);
  }

  function getTargetForCard(card) {
    if (!card || !hasServerList) return null;

    const pattern = readPattern(card);
    const index = getCardIndex(card);

    if (
      index >= 0 &&
      index < allTargets.length
    ) {
      const target = allTargets[index];

      if (
        target &&
        target.pattern.length === pattern.length
      ) {
        return {
          target,
          index
        };
      }
    }

    const matches = allTargets
      .map((target, targetIndex) => ({
        target,
        index: targetIndex
      }))
      .filter(entry =>
        entry.target.pattern === pattern
      );

    if (matches.length === 1) {
      return matches[0];
    }

    const currentIndex = allTargets.findIndex(
      target =>
        keyOf(target.id) ===
        keyOf(selectedTargetId)
    );

    if (
      currentIndex >= 0 &&
      allTargets[currentIndex].pattern === pattern
    ) {
      return {
        target: allTargets[currentIndex],
        index: currentIndex
      };
    }

    return null;
  }

  // ============================================
  // Saved incorrect guesses
  // ============================================

  function getRows(target) {
    if (!target) return [];

    const key = keyOf(target.id);

    if (!exclusions.has(key)) {
      exclusions.set(key, []);
    }

    return exclusions.get(key);
  }

  function restoreSavedRows(target) {
    if (!target || !target.fingerprint) return;

    const key = keyOf(target.id);
    const stored = saved[key];

    if (
      stored &&
      stored.fingerprint === target.fingerprint &&
      Array.isArray(stored.rows)
    ) {
      exclusions.set(
        key,
        stored.rows.map(row =>
          normaliseRow(row, target.pattern.length)
        )
      );
    } else {
      exclusions.set(key, []);
    }
  }

  function saveExclusions() {
    if (!hasServerList || waitingForTargets) return;

    const output = {};

    for (const target of allTargets) {
      const key = keyOf(target.id);

      const rows = (exclusions.get(key) || [])
        .map(row =>
          normaliseRow(row, target.pattern.length)
        )
        .filter(row => /[a-z0-9]/.test(row));

      if (rows.length && target.fingerprint) {
        output[key] = {
          fingerprint: target.fingerprint,
          rows
        };
      }
    }

    try {
      localStorage.setItem(
        STORAGE_KEY,
        JSON.stringify(output)
      );

      saved = output;
    } catch (error) {
      console.warn('[TCH] Save failed', error);
    }
  }

  function setRows(target, rows) {
    if (!target || target.temporary) return;

    exclusions.set(
      keyOf(target.id),
      rows.map(row =>
        normaliseRow(row, target.pattern.length)
      )
    );

    selectedCandidate = 0;
    lastSignature = '';

    saveExclusions();
    scheduleRefresh();
  }

  function addRow(target) {
    if (!target || target.temporary) return;

    const rows = [...getRows(target)];

    if (!rows.length) {
      rows.push(emptyRow(target.pattern.length));
    }

    rows.push(emptyRow(target.pattern.length));

    setRows(target, rows);
  }

  function removeRow(target, index) {
    if (!target || target.temporary) return;

    const rows = [...getRows(target)];

    rows.splice(index, 1);

    setRows(target, rows);
  }

  function updateRowCharacter(
    target,
    rowIndex,
    position,
    value
  ) {
    if (!target || target.temporary) return;

    const rows = [...getRows(target)];

    if (!rows[rowIndex]) return;

    const oldRow = normaliseRow(
      rows[rowIndex],
      target.pattern.length
    );

    rows[rowIndex] =
      oldRow.slice(0, position) +
      normaliseCharacter(value) +
      oldRow.slice(position + 1);

    setRows(target, rows);
  }

  function getExcludedPositions(target) {
    const excluded = new Map();

    for (const row of getRows(target)) {
      for (
        let position = 0;
        position < target.pattern.length;
        position++
      ) {
        const character = row[position];

        if (!/^[a-z0-9]$/.test(character || '')) {
          continue;
        }

        if (!excluded.has(position)) {
          excluded.set(position, new Set());
        }

        excluded.get(position).add(character);
      }
    }

    return excluded;
  }

  // ============================================
  // Server target list
  // ============================================

  function updateList(found) {
    if (!Array.isArray(found)) return;

    const previous = new Map(
      allTargets.map(target => [
        keyOf(target.id),
        target
      ])
    );

    const next = found
      .filter(target => target?.ID != null)
      .map(target => {
        const old = previous.get(keyOf(target.ID));

        return {
          id: target.ID,
          pattern:
            patternFromTarget(target) ||
            old?.pattern ||
            '',
          fingerprint: fingerprint(target),
          temporary: false
        };
      });

    const previousSelection =
      selectedTargetId == null
        ? null
        : keyOf(selectedTargetId);

    const activeIDs = new Set(
      next.map(target => keyOf(target.id))
    );

    for (const key of exclusions.keys()) {
      if (!activeIDs.has(key)) {
        exclusions.delete(key);
      }
    }

    for (const target of next) {
      const key = keyOf(target.id);
      const old = previous.get(key);

      if (
        !exclusions.has(key) ||
        (
          old &&
          old.fingerprint !== target.fingerprint
        )
      ) {
        restoreSavedRows(target);
      }
    }

    allTargets = next;
    hasServerList = true;
    waitingForTargets = false;

    const index = allTargets.findIndex(
      target =>
        keyOf(target.id) === previousSelection
    );

    if (index >= 0) {
      selectedTarget = index;
    } else {
      selectedTarget = Math.min(
        selectedTarget,
        Math.max(0, next.length - 1)
      );

      selectedCandidate = 0;
    }

    selectedTargetId =
      allTargets[selectedTarget]?.id ?? null;

    saveExclusions();

    lastSignature = '';
    scheduleRefresh();
  }

  // ============================================
  // Candidate matching
  // ============================================

  function matchesPattern(word, pattern) {
    if (word.length !== pattern.length) return false;

    for (let i = 0; i < pattern.length; i++) {
      if (
        pattern[i] !== '.' &&
        word[i] !== pattern[i]
      ) {
        return false;
      }
    }

    return true;
  }

  function isExcluded(word, excluded) {
    for (const [position, characters] of excluded) {
      if (characters.has(word[position])) {
        return true;
      }
    }

    return false;
  }

  function candidates(target) {
    if (!target || !wordCount || !target.pattern) {
      return [];
    }

    const pattern = target.pattern;
    const excluded = getExcludedPositions(target);
    const result = [];

    for (const word of byLength.get(pattern.length) || []) {
      if (
        matchesPattern(word, pattern) &&
        !isExcluded(word, excluded)
      ) {
        result.push(word);

        if (result.length >= MAX_CANDIDATES) {
          return result;
        }
      }
    }

    if (!result.length && pattern.length > 6) {
      for (
        let split = 3;
        split < 7 && split < pattern.length - 1;
        split++
      ) {
        const left = (
          byLength.get(split) || []
        )
          .filter(word =>
            matchesPattern(
              word,
              pattern.slice(0, split)
            )
          )
          .slice(0, 100);

        const right = (
          byLength.get(pattern.length - split) || []
        )
          .filter(word =>
            matchesPattern(
              word,
              pattern.slice(split)
            )
          )
          .slice(0, 100);

        for (const first of left) {
          for (const second of right) {
            const combined = first + second;

            if (!isExcluded(combined, excluded)) {
              result.push(combined);

              if (result.length >= MAX_CANDIDATES) {
                return result;
              }
            }
          }
        }

        if (result.length) break;
      }
    }

    return result;
  }

  // ============================================
  // Dictionary loading
  // ============================================

  function getText(url) {
    return new Promise((resolve, reject) => {
      if (typeof GM_xmlhttpRequest === 'function') {
        try {
          GM_xmlhttpRequest({
            method: 'GET',
            url,
            timeout: 45000,
            onload: response =>
              response.status >= 200 &&
              response.status < 300
                ? resolve(response.responseText)
                : reject(
                    new Error('HTTP ' + response.status)
                  ),
            onerror: () =>
              reject(new Error('Network error')),
            ontimeout: () =>
              reject(new Error('Request timed out'))
          });
        } catch (error) {
          reject(error);
        }
      } else {
        fetch(url)
          .then(response => {
            if (!response.ok) {
              throw new Error('HTTP ' + response.status);
            }

            return response.text();
          })
          .then(resolve, reject);
      }
    });
  }

  async function loadWords() {
    const id = ++requestId;

    loadState = 'Downloading ' + source + '…';
    byLength = new Map();
    wordCount = 0;

    updateToolbarStatus();
    lastSignature = '';
    scheduleRefresh();

    try {
      const raw = await getText(DATABASES[source]);

      if (id !== requestId) return;

      const map = new Map();

      for (const line of raw.split(/\r?\n/)) {
        const word = line.trim().toLowerCase();

        if (!word) continue;

        if (!map.has(word.length)) {
          map.set(word.length, []);
        }

        map.get(word.length).push(word);
        wordCount++;
      }

      byLength = map;

      loadState =
        wordCount.toLocaleString() +
        ' passwords loaded';
    } catch (error) {
      if (id !== requestId) return;

      loadState = 'Download failed: ' + error.message;
      console.error('[TCH]', error);
    }

    updateToolbarStatus();
    lastSignature = '';
    scheduleRefresh();
  }

  // ============================================
  // Global dictionary selector
  // ============================================

  function createToolbar() {
    if (toolbar) return;

    toolbar = el('div', 'tch-global-toolbar');
    toolbar.id = 'tch-global-toolbar';

    const label = el(
      'label',
      'tch-global-label',
      'Dictionary'
    );

    label.htmlFor = 'tch-global-source';

    toolbarSelect = el(
      'select',
      'tch-global-select'
    );

    toolbarSelect.id = 'tch-global-source';

    for (const key of Object.keys(DATABASES)) {
      const option = el('option', '', key);
      option.value = key;
      toolbarSelect.appendChild(option);
    }

    toolbarSelect.value = source;

    toolbarSelect.addEventListener(
      'change',
      event => {
        event.stopPropagation();

        source = toolbarSelect.value;

        try {
          localStorage.setItem(SOURCE_KEY, source);
        } catch (_) {}

        selectedCandidate = 0;
        loadWords();
      }
    );

    toolbarStatus = el(
      'span',
      'tch-global-status'
    );

    toolbarStatus.setAttribute(
      'aria-live',
      'polite'
    );

    toolbar.append(
      label,
      toolbarSelect,
      toolbarStatus
    );

    updateToolbarStatus();
  }

  function updateToolbarStatus() {
    if (!toolbarStatus) return;

    toolbarStatus.textContent =
      loadState.startsWith('Download failed')
        ? '!'
        : loadState.startsWith('Downloading')
          ? '…'
          : wordCount
            ? '✓'
            : '';

    toolbarStatus.title = loadState;

    toolbarStatus.classList.toggle(
      'tch-global-error',
      loadState.startsWith('Download failed')
    );

    if (toolbarSelect) {
      toolbarSelect.value = source;
    }
  }

  function isVisible(element) {
    if (!element?.isConnected) return false;

    const rect = element.getBoundingClientRect();

    return (
      rect.width > 0 &&
      rect.height > 0 &&
      getComputedStyle(element).display !== 'none'
    );
  }

  function findCrackingTitleBar() {
    if (!isCracking()) return null;

    const root = document.querySelector(
      '.cracking-root'
    );

    if (!root) return null;

    const currentCrime =
      root.querySelector('[class*="currentCrime"]');

    const searchRoot = currentCrime || root;

    const candidates = Array.from(
      searchRoot.querySelectorAll(
        'div, span, h1, h2, h3, strong'
      )
    );

    const titles = candidates.filter(element => {
      if (
        element.closest(
          '#tch-global-toolbar, #tch-embedded'
        )
      ) {
        return false;
      }

      if (!/^CRACKING$/i.test(
        (element.textContent || '').trim()
      )) {
        return false;
      }

      return isVisible(element);
    });

    for (const title of titles) {
      let parent = title.parentElement;

      for (let depth = 0; depth < 5 && parent; depth++) {
        const rect = parent.getBoundingClientRect();

        const hasCounters =
          /completed|success|failed/i.test(
            parent.textContent || ''
          ) ||
          parent.querySelectorAll('svg').length >= 2;

        if (
          rect.width >=
            document.documentElement.clientWidth * 0.65 &&
          rect.height >= 28 &&
          rect.height <= 85 &&
          (hasCounters || depth >= 1)
        ) {
          return parent;
        }

        parent = parent.parentElement;
      }
    }

    const possibleHeaders = Array.from(
      searchRoot.querySelectorAll(
        '[class*="header"], [class*="Header"], [class*="titleBar"], [class*="titlebar"]'
      )
    );

    for (const header of possibleHeaders) {
      const text = (
        header.textContent || ''
      ).trim();

      if (
        /^CRACKING/i.test(text) &&
        isVisible(header) &&
        header.getBoundingClientRect().height <= 85
      ) {
        return header;
      }
    }

    return null;
  }

  function attachToolbar() {
    if (!isCracking()) {
      if (toolbar?.isConnected) toolbar.remove();

      toolbarHost = null;
      return false;
    }

    createToolbar();

    const header = findCrackingTitleBar();

    if (!header) return false;

    if (
      toolbarHost &&
      toolbarHost !== header
    ) {
      toolbarHost.classList.remove(
        'tch-toolbar-host'
      );
    }

    toolbarHost = header;
    header.classList.add('tch-toolbar-host');

    if (toolbar.parentElement !== header) {
      toolbar.remove();
      header.appendChild(toolbar);
    }

    updateToolbarStatus();

    return true;
  }

  // ============================================
  // SPA navigation
  // ============================================

  function checkPageNavigation() {
    const currentLocation =
      location.pathname +
      location.search +
      location.hash;

    if (currentLocation === lastPageLocation) {
      return;
    }

    const wasCracking =
      /(?:^|\/)cracking(?:\/|$|\?)/i.test(
        lastPageLocation.split('#')[1] || ''
      );

    lastPageLocation = currentLocation;

    if (!isCracking()) {
      if (toolbar?.isConnected) toolbar.remove();
      if (panel?.isConnected) panel.remove();

      if (activeVirtualList) {
        restoreVirtualList(activeVirtualList);
        activeVirtualList = null;
      }

      toolbarHost = null;
      selectedCard = null;

      if (wasCracking) {
        hasServerList = false;
        waitingForTargets = true;
        allTargets = [];
        exclusions.clear();

        selectedTarget = 0;
        selectedTargetId = null;
        selectedCandidate = 0;
      }
    } else {
      if (!wasCracking) {
        waitingForTargets = !hasServerList;
      }

      attachToolbar();
    }

    lastSignature = '';
    scheduleRefresh();
  }

  function installNavigationWatcher() {
    window.addEventListener(
      'hashchange',
      checkPageNavigation
    );

    window.addEventListener(
      'popstate',
      checkPageNavigation
    );

    const targetWindow =
      typeof unsafeWindow !== 'undefined'
        ? unsafeWindow
        : window;

    try {
      for (const method of [
        'pushState',
        'replaceState'
      ]) {
        const original =
          targetWindow.history[method];

        if (typeof original !== 'function') continue;

        targetWindow.history[method] =
          function (...args) {
            const result = original.apply(this, args);

            setTimeout(checkPageNavigation, 0);

            return result;
          };
      }
    } catch (error) {
      console.warn(
        '[TCH] History monitoring unavailable',
        error
      );
    }

    checkPageNavigation();
  }

  // ============================================
  // Virtual list positioning
  // ============================================

  function getTranslateY(transform) {
    if (!transform || transform === 'none') {
      return 0;
    }

    const translate = transform.match(
      /translateY\(\s*(-?[\d.]+)px\s*\)/
    );

    if (translate) {
      return Number(translate[1]);
    }

    const translate3d = transform.match(
      /translate3d\(\s*[^,]+,\s*(-?[\d.]+)px/
    );

    if (translate3d) {
      return Number(translate3d[1]);
    }

    const matrix = transform.match(
      /matrix\(([^)]+)\)/
    );

    if (matrix) {
      const values = matrix[1]
        .split(',')
        .map(Number);

      return values[5] || 0;
    }

    return 0;
  }

  function getRowState(row) {
    const inlineTransform =
      row.style.transform || '';

    let state = rowState.get(row);

    if (!state) {
      state = {
        originalTransform: inlineTransform,
        originalHeight: row.style.height || '',
        appliedTransform: null,
        appliedHeight: null,
        baseY: getTranslateY(inlineTransform)
      };

      rowState.set(row, state);
      return state;
    }

    if (
      inlineTransform !== state.appliedTransform &&
      inlineTransform !== state.originalTransform
    ) {
      state.originalTransform = inlineTransform;
      state.baseY = getTranslateY(inlineTransform);
      state.appliedTransform = null;
    }

    const inlineHeight = row.style.height || '';

    if (
      inlineHeight !== state.appliedHeight &&
      inlineHeight !== state.originalHeight
    ) {
      state.originalHeight = inlineHeight;
      state.appliedHeight = null;
    }

    return state;
  }

  function setRowTransform(row, state, offset) {
    const desired = offset
      ? 'translateY(' +
        (state.baseY + offset) +
        'px)'
      : state.originalTransform;

    if (row.style.transform !== desired) {
      row.style.transform = desired;
    }

    state.appliedTransform = desired;
  }

  function setRowHeight(row, state, extra) {
    if (extra <= 0) {
      if (
        row.style.height !== state.originalHeight
      ) {
        row.style.height = state.originalHeight;
      }

      state.appliedHeight = state.originalHeight;
      return;
    }

    const original =
      parseFloat(state.originalHeight) || 51;

    const desired = (original + extra) + 'px';

    if (row.style.height !== desired) {
      row.style.height = desired;
    }

    state.appliedHeight = desired;
  }

  function getListState(list) {
    let state = listState.get(list);

    if (!state) {
      state = {
        originalHeight: list.style.height || '',
        appliedHeight: null
      };

      listState.set(list, state);
    }

    if (
      list.style.height !== state.appliedHeight &&
      list.style.height !== state.originalHeight
    ) {
      state.originalHeight = list.style.height || '';
      state.appliedHeight = null;
    }

    return state;
  }

  function setListExtraHeight(list, extra) {
    const state = getListState(list);

    if (extra <= 0) {
      if (
        list.style.height !== state.originalHeight
      ) {
        list.style.height = state.originalHeight;
      }

      state.appliedHeight = state.originalHeight;
      return;
    }

    const original =
      parseFloat(state.originalHeight) ||
      list.offsetHeight;

    const desired = (original + extra) + 'px';

    if (list.style.height !== desired) {
      list.style.height = desired;
    }

    state.appliedHeight = desired;
  }

  function restoreVirtualList(list) {
    if (!list) return;

    const rows = Array.from(
      list.querySelectorAll(ITEM_SELECTOR)
    );

    for (const row of rows) {
      const state = rowState.get(row);

      if (!state) continue;

      if (
        row.style.transform === state.appliedTransform
      ) {
        row.style.transform =
          state.originalTransform;
      }

      if (
        row.style.height === state.appliedHeight
      ) {
        row.style.height =
          state.originalHeight;
      }

      state.appliedTransform = null;
      state.appliedHeight = null;
    }

    const state = listState.get(list);

    if (state) {
      if (
        list.style.height === state.appliedHeight
      ) {
        list.style.height = state.originalHeight;
      }

      state.appliedHeight = null;
    }
  }

  function applyVirtualLayout() {
    if (applyingLayout) return;

    applyingLayout = true;

    try {
      if (!isCracking() || !panel?.isConnected) {
        if (activeVirtualList) {
          restoreVirtualList(activeVirtualList);
          activeVirtualList = null;
        }

        return;
      }

      const selectedRow =
        panel.closest(ITEM_SELECTOR);

      const list =
        selectedRow?.closest(LIST_SELECTOR);

      if (!selectedRow || !list) {
        if (activeVirtualList) {
          restoreVirtualList(activeVirtualList);
          activeVirtualList = null;
        }

        return;
      }

      if (
        activeVirtualList &&
        activeVirtualList !== list
      ) {
        restoreVirtualList(activeVirtualList);
      }

      activeVirtualList = list;

      const rows = Array.from(
        list.children
      ).filter(row =>
        row.matches(ITEM_SELECTOR)
      );

      const selectedState =
        getRowState(selectedRow);

      const selectedY =
        selectedState.baseY;

      const originalRowHeight =
        parseFloat(
          selectedState.originalHeight
        ) || 51;

      const wrapper =
        selectedRow.querySelector(
          '[class*="crimeOptionWrapper"]'
        );

      const contentHeight = wrapper
        ? wrapper.scrollHeight
        : originalRowHeight + panel.offsetHeight;

      const extraHeight = Math.max(
        0,
        Math.ceil(
          contentHeight - originalRowHeight
        )
      );

      for (const row of rows) {
        const state = getRowState(row);

        if (row === selectedRow) {
          setRowTransform(row, state, 0);
          setRowHeight(row, state, extraHeight);
          continue;
        }

        const isBelow =
          state.baseY >=
          selectedY + originalRowHeight - 1;

        setRowTransform(
          row,
          state,
          isBelow ? extraHeight : 0
        );

        setRowHeight(row, state, 0);
      }

      setListExtraHeight(list, extraHeight);
    } catch (error) {
      console.warn('[TCH] Layout error', error);
    } finally {
      applyingLayout = false;
    }
  }

  function scheduleLayout() {
    if (layoutFrame !== null) return;

    layoutFrame = requestAnimationFrame(() => {
      layoutFrame = null;
      applyVirtualLayout();
    });
  }

  // ============================================
  // Styles
  // ============================================

  function addStyles() {
    if (
      document.getElementById('tch-embedded-css')
    ) {
      return;
    }

    const style = el('style');
    style.id = 'tch-embedded-css';

    style.textContent = `
      .tch-toolbar-host {
        position: relative !important;
      }

      #tch-global-toolbar {
        position: absolute;
        top: 50%;
        right: 40%;
        left: auto;
        transform: translateY(-50%);
        z-index: 30;
        display: flex;
        align-items: center;
        justify-content: flex-end;
        gap: 5px;
        white-space: nowrap;
        font: 12px Arial, sans-serif;
        color: #ddd;
        pointer-events: auto;
        box-sizing: border-box;
      }

      #tch-global-toolbar * {
        box-sizing: border-box;
      }

      #tch-global-toolbar .tch-global-label {
        color: #ccc;
        font-size: 11px;
        font-weight: bold;
      }

      #tch-global-toolbar .tch-global-select {
        min-width: 62px;
        height: 27px;
        padding: 2px 5px;
        background: linear-gradient(
          #555,
          #363636
        );
        border: 1px solid #222;
        border-radius: 4px;
        box-shadow: inset 0 1px 0 #666;
        color: #eee;
        font: 12px Arial, sans-serif;
      }

      #tch-global-toolbar .tch-global-status {
        min-width: 10px;
        font-size: 12px;
        font-weight: bold;
        color: #87b957;
      }

      #tch-global-toolbar .tch-global-error {
        color: #ed8585;
      }

      @media (max-width: 430px) {
        #tch-global-toolbar {
          right: 40%;
          gap: 3px;
        }

        #tch-global-toolbar .tch-global-label {
          font-size: 10px;
        }

        #tch-global-toolbar .tch-global-select {
          min-width: 57px;
          max-width: 65px;
        }
      }

      #tch-embedded {
        position: relative;
        display: block;
        width: 100%;
        max-width: 100%;
        margin: 0;
        background: #333;
        color: #ddd;
        border: 1px solid #484848;
        border-top: 1px solid #555;
        border-radius: 0 0 5px 5px;
        box-shadow: inset 0 1px 0 #383838;
        font-family: Arial, Helvetica, sans-serif;
        font-size: 12px;
        line-height: 1.4;
        overflow: hidden;
        box-sizing: border-box;
        clear: both;
        transform: none !important;
      }

      #tch-embedded * {
        box-sizing: border-box;
      }

      #tch-embedded .tch-head {
        min-height: 37px;
        background: linear-gradient(
          #414141,
          #363636
        );
        border-bottom: 1px solid #252525;
        padding: 6px 10px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 8px;
      }

      #tch-embedded .tch-heading {
        color: #e6e6e6;
        font-family: "Arial Narrow", Arial, sans-serif;
        font-size: 14px;
        font-weight: bold;
      }

      #tch-embedded .tch-body {
        padding: 10px;
        display: grid;
        gap: 9px;
        background: #303030;
      }

      #tch-embedded.tch-collapsed .tch-body {
        display: none;
      }

      #tch-embedded .tch-row {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 8px;
      }

      #tch-embedded .tch-row > * {
        min-width: 0;
      }

      #tch-embedded button {
        font: inherit;
        color: #e0e0e0;
        background: linear-gradient(
          #505050,
          #3a3a3a
        );
        border: 1px solid #242424;
        border-radius: 4px;
        box-shadow: inset 0 1px 0 #646464;
        padding: 5px 9px;
        min-height: 29px;
        cursor: pointer;
      }

      #tch-embedded button:active {
        background: #292929;
        box-shadow: inset 0 1px 3px #111;
      }

      #tch-embedded button:disabled {
        opacity: .4;
        cursor: default;
      }

      #tch-embedded .tch-toggle {
        min-width: 28px;
        min-height: 27px;
        padding: 2px 7px;
        font-size: 18px;
        font-weight: bold;
        line-height: 1;
      }

      #tch-embedded .tch-candidate-title {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 8px;
        color: #aaa;
        font-size: 11px;
      }

      #tch-embedded .tch-answer {
        flex: 1;
        text-align: center;
        font: bold 20px monospace;
        letter-spacing: 1px;
        color: #f0f0f0;
        overflow-wrap: anywhere;
      }

      #tch-embedded .tch-answer-empty {
        font: 12px Arial, Helvetica, sans-serif;
        letter-spacing: 0;
        color: #aaa;
      }

      #tch-embedded .tch-candidate-button {
        min-width: 49px;
      }

      #tch-embedded .tch-divider {
        border-top: 1px solid #494949;
        margin-top: 2px;
        padding-top: 10px;
      }

      #tch-embedded .tch-section-title {
        font-size: 12px;
        font-weight: bold;
        color: #ddd;
      }

      #tch-embedded .tch-exclusion-list {
        display: grid;
        gap: 6px;
        margin-top: 8px;
        max-height: 200px;
        overflow-y: auto;
      }

      #tch-embedded .tch-exclusion-row {
        display: flex;
        align-items: center;
        gap: 5px;
      }

      #tch-embedded .tch-exclusion-cells {
        display: flex;
        align-items: center;
        justify-content: center;
        flex: 1;
        gap: 4px;
        min-width: 0;
      }

      #tch-embedded .tch-exclusion-cell {
        width: 25px;
        min-width: 0;
        height: 29px;
        padding: 2px 0;
        text-align: center;
        background: #252525;
        color: #e5a09a;
        border: 1px solid #555;
        border-radius: 2px;
        box-shadow: inset 0 1px 2px #171717;
        font: bold 15px monospace;
        text-transform: uppercase;
        outline: none;
      }

      #tch-embedded .tch-exclusion-cell:focus {
        border-color: #91a56e;
        background: #30352b;
      }

      #tch-embedded .tch-exclusion-cell::placeholder {
        color: #777;
        opacity: 1;
      }

      #tch-embedded .tch-remove-button {
        min-width: 29px;
        padding: 3px 7px;
        background: linear-gradient(
          #66413f,
          #4b3030
        );
        border-color: #382525;
        color: #e7c3c1;
        font-weight: bold;
      }

      #tch-embedded .tch-add-button {
        min-width: 32px;
        padding: 3px 8px;
        background: linear-gradient(
          #5a7645,
          #405a32
        );
        border-color: #2e4325;
        color: #edf3e8;
        font-size: 17px;
        font-weight: bold;
      }

      #tch-embedded .tch-exclusion-note {
        font-size: 10px;
        color: #999;
        line-height: 1.4;
      }

      #tch-embedded .tch-muted {
        font-size: 11px;
        color: #999;
      }

      #tch-embedded .tch-loading {
        display: flex;
        align-items: center;
        justify-content: center;
        gap: 10px;
        min-height: 55px;
        color: #bbb;
        font-size: 12px;
      }

      #tch-embedded .tch-spinner {
        width: 17px;
        height: 17px;
        border: 2px solid #555;
        border-top-color: #9fbd78;
        border-radius: 50%;
        animation: tch-spin .75s linear infinite;
        flex-shrink: 0;
      }

      @keyframes tch-spin {
        to {
          transform: rotate(360deg);
        }
      }

      @media (max-width: 420px) {
        #tch-embedded .tch-body {
          padding: 9px 8px;
        }

        #tch-embedded .tch-exclusion-cells {
          gap: 3px;
        }

        #tch-embedded .tch-exclusion-cell {
          width: 24px;
        }
      }
    `;

    (
      document.head ||
      document.documentElement
    ).appendChild(style);
  }

  function makeButton(
    label,
    callback,
    className = ''
  ) {
    const button = el(
      'button',
      className,
      label
    );

    button.type = 'button';

    button.addEventListener(
      'click',
      event => {
        event.preventDefault();
        event.stopPropagation();
        callback();
      }
    );

    return button;
  }

  // ============================================
  // Embedded panel
  // ============================================

  function createPanel() {
    if (panel) return;

    panel = el('div');
    panel.id = 'tch-embedded';
    panel.classList.add('tch-collapsed');

    const header = el('div', 'tch-head');

    header.appendChild(
      el(
        'span',
        'tch-heading',
        'Cracking Helper'
      )
    );

    const toggle = makeButton(
      '+',
      () => {
        collapsed = !collapsed;

        panel.classList.toggle(
          'tch-collapsed',
          collapsed
        );

        toggle.textContent =
          collapsed ? '+' : '−';

        scheduleLayout();
      },
      'tch-toggle'
    );

    toggle.removeAttribute('title');

    header.appendChild(toggle);

    panel.appendChild(header);
    panel.appendChild(
      el('div', 'tch-body')
    );
  }

  // ============================================
  // Password card selection
  // ============================================

  function findSelectedCard() {
    const cards = Array.from(
      document.querySelectorAll('.crime-option')
    );

    if (!cards.length) return null;

    if (
      selectedCard &&
      selectedCard.isConnected &&
      cards.includes(selectedCard)
    ) {
      return selectedCard;
    }

    if (!hasServerList) {
      return cards[
        Math.min(selectedTarget, cards.length - 1)
      ] || null;
    }

    const target = allTargets[selectedTarget];

    if (!target) return null;

    for (const card of cards) {
      const resolved = getTargetForCard(card);

      if (
        resolved &&
        keyOf(resolved.target.id) ===
          keyOf(target.id)
      ) {
        return card;
      }
    }

    return null;
  }

  function attachPanel() {
    if (!panel || !isCracking()) return;

    const card = findSelectedCard();

    if (!card) {
      if (panel.isConnected) panel.remove();

      scheduleLayout();
      return;
    }

    selectedCard = card;

    if (panel.parentElement !== card) {
      panel.remove();
      card.appendChild(panel);
    }

    scheduleLayout();
  }

  function resolveTargetForCard(card) {
    return getTargetForCard(card);
  }

  // ============================================
  // Incorrect guess editor
  // ============================================

  function buildExclusionEditor(body, target) {
    const section = el(
      'div',
      'tch-divider'
    );

    section.appendChild(
      el(
        'div',
        'tch-section-title',
        'Incorrect Guesses'
      )
    );

    const list = el(
      'div',
      'tch-exclusion-list'
    );

    section.appendChild(list);

    const rows = getRows(target);

    const displayRows = rows.length
      ? rows
      : [emptyRow(target.pattern.length)];

    displayRows.forEach((row, rowIndex) => {
      const rowElement = el(
        'div',
        'tch-exclusion-row'
      );

      const cells = el(
        'div',
        'tch-exclusion-cells'
      );

      for (
        let position = 0;
        position < target.pattern.length;
        position++
      ) {
        const input = el(
          'input',
          'tch-exclusion-cell'
        );

        input.type = 'text';
        input.maxLength = 1;
        input.autocomplete = 'off';
        input.autocapitalize = 'characters';
        input.spellcheck = false;

        input.dataset.row = String(rowIndex);
        input.dataset.position = String(position);

        const character = row[position] || '.';

        input.value =
          character === '.'
            ? ''
            : character.toUpperCase();

        input.placeholder = '_';

        input.setAttribute(
          'aria-label',
          'Incorrect character at position ' +
            (position + 1)
        );

        input.addEventListener('input', () => {
          const character =
            normaliseCharacter(input.value);

          input.value =
            character === '.'
              ? ''
              : character.toUpperCase();

          if (getRows(target).length === 0) {
            exclusions.set(
              keyOf(target.id),
              [emptyRow(target.pattern.length)]
            );
          }

          updateRowCharacter(
            target,
            rowIndex,
            position,
            character
          );
        });

        cells.appendChild(input);
      }

      rowElement.appendChild(cells);

      const remove = makeButton(
        '×',
        () => removeRow(target, rowIndex),
        'tch-remove-button'
      );

      rowElement.appendChild(remove);
      list.appendChild(rowElement);
    });

    const controls = el(
      'div',
      'tch-row'
    );

    controls.appendChild(
      el(
        'span',
        'tch-exclusion-note',
        'Add a new row if required.'
      )
    );

    controls.appendChild(
      makeButton(
        '+',
        () => addRow(target),
        'tch-add-button'
      )
    );

    section.appendChild(controls);
    body.appendChild(section);
  }

  function showLoading(body, message) {
    const loading = el(
      'div',
      'tch-loading'
    );

    loading.appendChild(
      el('span', 'tch-spinner')
    );

    loading.appendChild(
      el('span', '', message)
    );

    body.appendChild(loading);
  }

  // ============================================
  // Rendering
  // ============================================

  function refresh() {
    if (!document.body) return;

    checkPageNavigation();

    if (!isCracking()) {
      if (panel?.isConnected) panel.remove();
      if (toolbar?.isConnected) toolbar.remove();

      selectedCard = null;
      lastSignature = '';

      if (activeVirtualList) {
        restoreVirtualList(activeVirtualList);
        activeVirtualList = null;
      }

      return;
    }

    addStyles();
    createPanel();
    attachToolbar();

    const targets = readTargets();

    let active = null;
    let targetReady = false;

    if (selectedCard?.isConnected) {
      const resolved =
        resolveTargetForCard(selectedCard);

      if (resolved) {
        selectedTarget = resolved.index;
        selectedTargetId = resolved.target.id;
        active = resolved.target;
        targetReady = true;
      }
    }

    if (!active && hasServerList) {
      const index = allTargets.findIndex(
        target =>
          keyOf(target.id) ===
          keyOf(selectedTargetId)
      );

      if (index >= 0) {
        selectedTarget = index;
      }

      active = allTargets[selectedTarget] || null;

      if (active) {
        selectedTargetId = active.id;
        targetReady = true;
      }
    }

    if (!active && !hasServerList) {
      active = targets[selectedTarget];
    }

    attachPanel();

    const signature = JSON.stringify([
      source,
      loadState,
      wordCount,
      selectedTarget,
      selectedTargetId,
      selectedCandidate,
      waitingForTargets,
      targetReady,
      selectedCard
        ? readPattern(selectedCard)
        : null,
      targets.map(target => [
        target.id,
        target.pattern
      ]),
      active && targetReady
        ? getRows(active)
        : null
    ]);

    if (signature === lastSignature) {
      scheduleLayout();
      return;
    }

    lastSignature = signature;

    const body = panel.querySelector('.tch-body');

    let focusInfo = null;

    const focused = document.activeElement;

    if (
      focused &&
      panel.contains(focused) &&
      focused.classList.contains(
        'tch-exclusion-cell'
      )
    ) {
      focusInfo = {
        row: focused.dataset.row,
        position: focused.dataset.position,
        start: focused.selectionStart,
        end: focused.selectionEnd
      };
    }

    body.replaceChildren();

    if (
      waitingForTargets ||
      !hasServerList
    ) {
      showLoading(
        body,
        'Loading password data…'
      );

      scheduleLayout();
      return;
    }

    if (!targetReady || !active) {
      body.appendChild(
        el(
          'div',
          'tch-muted',
          'Unable to identify this password.'
        )
      );

      scheduleLayout();
      return;
    }

    if (!wordCount) {
      showLoading(
        body,
        loadState.startsWith('Download failed')
          ? loadState
          : 'Loading dictionary…'
      );

      buildExclusionEditor(body, active);

      scheduleLayout();
      return;
    }

    const results = candidates(active);

    selectedCandidate = Math.max(
      0,
      Math.min(
        selectedCandidate,
        results.length - 1
      )
    );

    const candidateTitle = el(
      'div',
      'tch-candidate-title'
    );

    candidateTitle.appendChild(
      el(
        'span',
        '',
        'Top ' +
          (results.length || MAX_CANDIDATES) +
          ' Candidates'
      )
    );

    candidateTitle.appendChild(
      el(
        'span',
        '',
        results.length
          ? (selectedCandidate + 1) +
            ' / ' +
            results.length
          : '0 / 0'
      )
    );

    body.appendChild(candidateTitle);

    const answerRow = el(
      'div',
      'tch-row'
    );

    const previousCandidate = makeButton(
      'Prev',
      () => {
        selectedCandidate = Math.max(
          0,
          selectedCandidate - 1
        );

        lastSignature = '';
        refresh();
      },
      'tch-candidate-button'
    );

    const nextCandidate = makeButton(
      'Next',
      () => {
        selectedCandidate = Math.min(
          results.length - 1,
          selectedCandidate + 1
        );

        lastSignature = '';
        refresh();
      },
      'tch-candidate-button'
    );

    previousCandidate.disabled =
      selectedCandidate === 0;

    nextCandidate.disabled =
      selectedCandidate >= results.length - 1;

    const answer = el(
      'span',
      'tch-answer',
      results.length
        ? results[selectedCandidate].toUpperCase()
        : 'No password candidates'
    );

    if (!results.length) {
      answer.classList.add(
        'tch-answer-empty'
      );
    }

    answerRow.append(
      previousCandidate,
      answer,
      nextCandidate
    );

    body.appendChild(answerRow);

    buildExclusionEditor(body, active);

    if (focusInfo) {
      const replacement = Array.from(
        body.querySelectorAll(
          '.tch-exclusion-cell'
        )
      ).find(input =>
        input.dataset.row === focusInfo.row &&
        input.dataset.position ===
          focusInfo.position
      );

      if (replacement) {
        try {
          replacement.focus({
            preventScroll: true
          });

          replacement.setSelectionRange(
            focusInfo.start ?? 0,
            focusInfo.end ?? 0
          );
        } catch (_) {}
      }
    }

    scheduleLayout();
  }

  function scheduleRefresh() {
    if (refreshTimer) return;

    refreshTimer = setTimeout(() => {
      refreshTimer = null;

      try {
        refresh();
      } catch (error) {
        console.error(
          '[TCH] Render error',
          error
        );
      }
    }, 150);
  }

  // ============================================
  // Network response listener
  // ============================================

  function inspectResponse(data) {
    const found =
      data?.DB?.crimesByType?.targets;

    if (Array.isArray(found)) {
      updateList(found);
    }
  }

  function watchResponses() {
    const targetWindow =
      typeof unsafeWindow !== 'undefined'
        ? unsafeWindow
        : window;

    const original = targetWindow.fetch;

    if (typeof original !== 'function') return;

    try {
      targetWindow.fetch =
        function (...args) {
          const promise = original.apply(this, args);

          try {
            const input = args[0];

            const url =
              typeof input === 'string'
                ? input
                : input?.url;

            if (
              url &&
              /sid=crimesData/.test(url)
            ) {
              promise
                .then(response =>
                  response.clone().json()
                )
                .then(inspectResponse)
                .catch(() => {});
            }
          } catch (_) {}

          return promise;
        };
    } catch (error) {
      console.warn(
        '[TCH] Fetch interception unavailable',
        error
      );
    }
  }

  // ============================================
  // Select password by tapping its slots
  // ============================================

  function installTargetSelection() {
    document.addEventListener(
      'click',
      event => {
        if (
          !isCracking() ||
          !(event.target instanceof Element) ||
          event.target.closest(
            '#tch-embedded, #tch-global-toolbar'
          )
        ) {
          return;
        }

        const slot = event.target.closest(
          'div[class*="charSlot"]'
        );

        const card = slot?.closest(
          '.crime-option'
        );

        if (!card) return;

        selectedCard = card;

        const resolved =
          resolveTargetForCard(card);

        if (resolved) {
          selectedTarget = resolved.index;
          selectedTargetId = resolved.target.id;
          waitingForTargets = false;
        } else {
          selectedTargetId = null;
        }

        selectedCandidate = 0;
        lastSignature = '';

        scheduleRefresh();
      },
      true
    );
  }

  // ============================================
  // Initialise
  // ============================================

  function init() {
    if (initialized) return;
    initialized = true;

    watchResponses();
    installTargetSelection();
    installNavigationWatcher();

    const observer = new MutationObserver(
      mutations => {
        let needsRefresh = false;
        let needsLayout = false;
        let needsToolbar = false;

        for (const mutation of mutations) {
          const target = mutation.target;

          if (
            target instanceof Element &&
            target.closest(
              '#tch-embedded, #tch-global-toolbar'
            )
          ) {
            continue;
          }

          if (mutation.type === 'attributes') {
            if (
              target instanceof Element &&
              (
                target.matches(ITEM_SELECTOR) ||
                target.matches(LIST_SELECTOR)
              )
            ) {
              needsLayout = true;
            }

            continue;
          }

          if (mutation.type === 'childList') {
            needsRefresh = true;

            if (isCracking()) {
              needsToolbar = true;
            }
          }

          if (mutation.type === 'characterData') {
            needsRefresh = true;
          }
        }

        if (
          needsToolbar &&
          (
            !toolbar?.isConnected ||
            !toolbarHost?.isConnected
          )
        ) {
          attachToolbar();
        }

        if (needsRefresh) {
          scheduleRefresh();
        } else if (needsLayout) {
          scheduleLayout();
        }
      }
    );

    observer.observe(
      document.body,
      {
        childList: true,
        subtree: true,
        characterData: true,
        attributes: true,
        attributeFilter: ['style']
      }
    );

    window.addEventListener(
      'resize',
      () => {
        scheduleLayout();
        attachToolbar();
      }
    );

    window.addEventListener(
      'scroll',
      scheduleLayout,
      { passive: true }
    );

    if (window.visualViewport) {
      window.visualViewport.addEventListener(
        'resize',
        scheduleLayout
      );
    }

    setInterval(() => {
      checkPageNavigation();

      if (isCracking()) {
        if (
          !toolbar?.isConnected ||
          !toolbarHost?.isConnected
        ) {
          attachToolbar();
        }

        scheduleRefresh();
        scheduleLayout();
      }
    }, 500);

    scheduleRefresh();
    loadWords();
  }

  if (document.body) {
    init();
  } else {
    document.addEventListener(
      'DOMContentLoaded',
      init,
      { once: true }
    );
  }
})();
