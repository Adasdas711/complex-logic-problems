/* Сборник занятий по «Комплексной логике». Данные — site_src/data (собирает src/scripts/site.py).
   Адреса: #/ — курс, #/z/76 — занятие, #/m/7 — модуль, #/k, #/k/10 — контрольные, #/t, #/t/12 — входные тесты,
   #/poisk/запрос, #/oboz — обозначения, #/ustr — как устроены задачи.
   Отметки «выполнено» и «решена» хранятся только в localStorage этого браузера. */
'use strict';

const DATA = 'site_src/data/';
const KEY = 'kl-zadachnik-v1';
const cache = {};
let IDX = null;
let route = { page: 'kurs' };
const open = new Set(); // раскрытые ответы и решения: "a:id", "s:id", "e:id"

// ---------- хранение ----------
const S = (() => {
  let st = {};
  try { st = JSON.parse(localStorage.getItem(KEY) || '{}') || {}; } catch (e) { st = {}; }
  st.z = st.z || {}; st.k = st.k || {}; st.t = st.t || {}; st.r = st.r || {};
  st.mode = st.mode || 'end';
  if (st.side === undefined) st.side = true;
  return st;
})();
function save() { try { localStorage.setItem(KEY, JSON.stringify(S)); } catch (e) { /* хранилище недоступно */ } }

// ---------- помощники ----------
const $ = (sel, root = document) => root.querySelector(sel);
const esc = (s) => String(s ?? '').replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
function get(path) {
  if (!cache[path]) {
    cache[path] = fetch(DATA + path, { cache: 'no-cache' }).then((r) => { if (!r.ok) throw new Error(path); return r.json(); })
      .catch((e) => { delete cache[path]; throw e; });
  }
  return cache[path];
}
const pad = (n) => String(n).padStart(2, '0');
function plural(n, one, few, many) {
  const a = n % 10, b = n % 100;
  if (a === 1 && b !== 11) return one;
  if (a >= 2 && a <= 4 && (b < 12 || b > 14)) return few;
  return many;
}
const ROM = (m) => IDX.modules[m].name.split('. ')[0];
const modTitle = (m) => IDX.modules[m].name.split('. ').slice(1).join('. ');
function sessionsWord(list) {
  if (!list || !list.length) return '';
  const r = [];
  let a = list[0], b = list[0];
  for (const x of list.slice(1).concat([null])) {
    if (x === b + 1) { b = x; continue; }
    r.push(a === b ? String(a) : (b === a + 1 ? a + ', ' + b : a + '–' + b));
    if (x !== null) { a = b = x; }
  }
  return (list.length === 1 ? 'занятие ' : 'занятия ') + r.join(', ');
}
const SUP = { 'ˢ': 's', 'ᵉ': 'e', 'ᵐ': 'm', '¹': '1', '²': '2', '³': '3', '⁵': '5', 'ʷ': 'w', 'ʳ': 'r', 'ⁱ': 'i', 'ᶜ': 'c', 'ⁿ': 'n', 'ᵖ': 'p', 'ᵏ': 'k', 'ᵗ': 't', '₁': '1', '₂': '2' };
const fold = (s) => String(s).toLowerCase().replace(/ё/g, 'е').replace(/[ˢᵉᵐ¹²³⁵ʷʳⁱᶜⁿᵖᵏᵗ₁₂]/g, (c) => SUP[c] || c).replace(/[\^_{}*]/g, '');

function findSessions(q) {
  q = (q || '').trim().toLowerCase();
  if (!q) return [];
  const num = q.replace(/^(занятие|зан\.?)\s*/, '');
  if (/^\d+$/.test(num)) return IDX.sessions.filter((s) => String(s.num).startsWith(num));
  const words = fold(q).split(/\s+/).filter(Boolean);
  return IDX.sessions.filter((s) => {
    const hay = fold(s.topic + ' ' + s.label + ' ' + IDX.modules[s.module].name);
    return words.every((w) => hay.includes(w));
  });
}
const doneZ = (n) => !!S.z[n];
const doneK = (k) => !!S.k[k];
const doneT = (c) => !!S.t[c];
function modSessions(m) { return IDX.sessions.filter((s) => s.module === m); }
function testBefore(num) { return IDX.tests.filter((t) => t.before === num); }
function kontrolAfter(num) { return IDX.kontrol.filter((k) => k.after === num); }
const testTo = (t) => (t.chapter === 16 ? 'К разделу 16' : 'К главе ' + t.chapter) + '. ' + t.titleH.replace(/^(Глава|Раздел) \d+\. /, '');
const testShort = (t) => (t.chapter === 16 ? 'разделу 16' : 'главе ' + t.chapter);

const searchIcon = (s = 16) => `<svg width="${s}" height="${s}" viewBox="0 0 24 24" fill="none" stroke="#8c8c8c" stroke-width="2" aria-hidden="true"><circle cx="11" cy="11" r="7"></circle><path d="M20 20l-4-4"></path></svg>`;

// ---------- боковое меню ----------
function renderSide() {
  const side = $('#side');
  side.classList.toggle('collapsed', !S.side);
  if (!S.side) {
    side.innerHTML = `<button type="button" class="btn side-btn" data-act="side" aria-label="Развернуть меню" title="Развернуть меню">›</button>`;
    return;
  }
  const act = route.page;
  const mods = IDX.modules.map((m, i) => {
    const ss = modSessions(i), d = ss.filter((s) => doneZ(s.num)).length, all = ss.length;
    const nums = ss.map((s) => s.num);
    const on = act === 'mod' && route.m === i || act === 'z' && route.mod === i;
    if (!all) return `<a class="nav${on ? ' on' : ''}" href="#/m/${i + 1}"><span class="t1">${esc(m.name)}</span><span class="t2"><span>занятия готовятся</span></span></a>`;
    return `<a class="nav${on ? ' on' : ''}" href="#/m/${i + 1}"><span class="t1">${esc(m.name)}</span>
      <span class="t2"><span>занятия ${Math.min(...nums)}–${Math.max(...nums)}</span><span class="pr${d === all ? ' ok' : ''}">${d === all ? '✓ выполнено' : 'выполнено ' + d + ' из ' + all}</span></span>
      <span class="bar"><span style="width:${Math.round(100 * d / all)}%"></span></span></a>`;
  }).join('');
  const kd = IDX.kontrol.filter((k) => doneK(k.k)).length, td = IDX.tests.filter((t) => doneT(t.chapter)).length;
  side.innerHTML = `
    <div class="side-top"><button type="button" class="btn side-btn" data-act="side">‹ Свернуть</button></div>
    <div class="side-search">
      <label for="side-q">Поиск занятия</label>
      <div class="field">${searchIcon()}<input id="side-q" type="search" autocomplete="off" placeholder="Номер или название"></div>
      <div class="drop" id="side-drop" hidden></div>
    </div>
    <a class="nav${act === 'kurs' ? ' on' : ''}" href="#/"><span class="t1">Курс</span><span class="t2"><span>все занятия, поиск</span></span></a>
    <p class="side-h">Модули</p>${mods}
    <p class="side-h">Проверка</p>
    <a class="nav${act === 'kontr' || act === 'k' ? ' on' : ''}" href="#/k"><span class="t1">Контрольные</span><span class="t2"><span>${IDX.kontrol.length} работ · <span class="${kd === IDX.kontrol.length ? 'ok' : ''}">выполнено ${kd}</span></span></span></a>
    <a class="nav${act === 'vhod' || act === 't' ? ' on' : ''}" href="#/t"><span class="t1">Входные тесты</span><span class="t2"><span>${IDX.tests.length} тестов · <span class="${td === IDX.tests.length ? 'ok' : ''}">выполнено ${td}</span></span></span></a>
    <p class="side-h">Справка</p>
    <a class="nav${act === 'oboz' ? ' on' : ''}" href="#/oboz"><span class="t1">Обозначения</span><span class="t2"><span>символы книги</span></span></a>
    <a class="nav${act === 'ustr' ? ' on' : ''}" href="#/ustr"><span class="t1">Как устроены задачи</span><span class="t2"><span>ступени и типы</span></span></a>
    <p class="side-note">Отметки «выполнено» хранятся только в этом браузере.</p>`;
  const inp = $('#side-q'), drop = $('#side-drop');
  inp.addEventListener('input', () => {
    const q = inp.value, found = findSessions(q);
    if (!q.trim()) { drop.hidden = true; return; }
    drop.hidden = false;
    drop.innerHTML = found.slice(0, 6).map((s) => `<a href="#/z/${s.num}"><b>${s.num}</b><span>${s.topicH}</span></a>`).join('')
      + (found.length ? '' : '<p>Ничего не найдено</p>')
      + (found.length > 6 ? `<a class="more" href="#/poisk/${encodeURIComponent(q.trim())}">и ещё ${found.length - 6} — все результаты</a>` : '');
  });
  inp.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      const found = findSessions(inp.value);
      location.hash = found.length === 1 ? '#/z/' + found[0].num : '#/poisk/' + encodeURIComponent(inp.value.trim());
    } else if (e.key === 'Escape') { inp.value = ''; drop.hidden = true; }
  });
  inp.addEventListener('blur', () => setTimeout(() => { drop.hidden = true; }, 150));
}

// ---------- курс ----------
function resultsHtml(found, limit) {
  return found.slice(0, limit).map((s) => `<a class="res" href="#/z/${s.num}"><b>${s.num}</b><span class="tt">${s.topicH}</span>
    ${doneZ(s.num) ? '<span class="ok">✓ выполнено</span>' : ''}<span class="meta">неделя ${s.week} · ${esc(s.label)}</span></a>`).join('');
}
function viewKurs() {
  const blocks = IDX.modules.map((m, i) => {
    const ss = modSessions(i);
    const items = [];
    for (const s of ss) {
      for (const t of testBefore(s.num)) {
        items.push(`<a class="tile gold${doneT(t.chapter) ? ' done' : ''}" href="#/t/${t.chapter}" title="Входной тест к ${testShort(t)}">${doneT(t.chapter) ? '<span class="ck">✓</span>' : ''}<span class="n">Т</span><span class="s">${t.chapter === 16 ? 'тест р. 16' : 'тест гл. ' + t.chapter}</span></a>`);
      }
      items.push(`<a class="tile${doneZ(s.num) ? ' done' : ''}" data-n="${s.num}" href="#/z/${s.num}" title="${esc(s.topic)}">${doneZ(s.num) ? '<span class="ck" aria-label="выполнено">✓</span>' : ''}<span class="n">${s.num}</span><span class="s">${esc(s.label)}</span></a>`);
      for (const k of kontrolAfter(s.num)) {
        items.push(`<a class="tile gold${doneK(k.k) ? ' done' : ''}" href="#/k/${k.k}" title="Контрольная работа ${k.k}">${doneK(k.k) ? '<span class="ck">✓</span>' : ''}<span class="n">К</span><span class="s">контр. ${k.k}</span></a>`);
      }
    }
    const nums = ss.map((s) => s.num);
    if (!nums.length) return `<div class="mod-block"><p>${esc(m.name)} <span>· занятия готовятся</span></p></div>`;
    return `<div class="mod-block"><p>${esc(m.name)} <span>· занятия ${Math.min(...nums)}–${Math.max(...nums)}</span></p><div class="tiles">${items.join('')}</div></div>`;
  }).join('');
  const total = IDX.sessions.filter((s) => doneZ(s.num)).length;
  $('#view').innerHTML = `
    <header class="head"><h1 class="big-h1">Комплексная логика</h1>
      <p>Задачник по книге А. А. Зиновьева (1970): ${IDX.sessions.length} занятий, ${IDX.kontrol.length} контрольных, ${IDX.tests.length} входных тестов · выполнено занятий: ${total}</p></header>
    <section class="card">
      <label for="main-q" class="eyebrow">Поиск занятия</label>
      <div class="field">${searchIcon(18)}<input id="main-q" type="search" autocomplete="off" placeholder="Номер занятия или слова из названия: 76, кванторы, модальная логика"><button type="button" class="btn sm" id="main-clear" hidden>Очистить</button></div>
      <div id="main-res" hidden><p class="small muted" id="main-count" style="margin:0 0 8px"></p><div class="results" id="main-list"></div></div>
    </section>
    <section class="card"><h2 class="eyebrow">Как заниматься</h2>
      <ul class="plain-list">
        <li>Занятие — 4–6 часов, два раза в неделю: 90 занятий за 45 недель.</li>
        <li>Порядок: прочитать страницы книги → разобрать примеры решений → решить задачи на бумаге → сверить с ответами.</li>
        <li>Ответ и решение открывать только после своего решения. Задачи с ошибками — решить снова через неделю.</li>
        <li>Решили занятие — нажмите «Отметить занятие выполненным»: плитка и модуль в меню станут зелёными.</li>
        <li>Перед новой главой — входной тест (<b style="color:var(--gold)">Т</b>), раз в месяц — контрольная (<b style="color:var(--gold)">К</b>).</li>
      </ul></section>
    <section class="card">
      <div class="row-between"><h2 class="eyebrow">Занятия 1–${IDX.sessions.length}</h2>
        <p class="legend"><span class="g">Т</span> входной тест · <span class="g">К</span> контрольная · <span class="ok">✓</span> выполнено</p></div>
      ${blocks}
    </section>`;
  const inp = $('#main-q'), res = $('#main-res'), clear = $('#main-clear');
  const upd = () => {
    const q = inp.value.trim(), found = findSessions(q), hit = new Set(found.map((s) => s.num));
    res.hidden = !q; clear.hidden = !q;
    document.querySelectorAll('.tile').forEach((t) => t.classList.toggle('dim', !!q && !hit.has(+t.dataset.n)));
    if (!q) return;
    $('#main-count').textContent = found.length ? 'Найдено ' + plural(found.length, 'занятие', 'занятия', 'занятий') + ': ' + found.length
      : 'Ничего не найдено. Попробуйте номер (76) или слово из темы (кванторы).';
    $('#main-list').innerHTML = resultsHtml(found, 8) + (found.length > 8 ? `<a class="btn sm" href="#/poisk/${encodeURIComponent(q)}">Все ${found.length} результатов</a>` : '');
  };
  inp.addEventListener('input', upd);
  inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') { const f = findSessions(inp.value); if (f.length) location.hash = '#/z/' + f[0].num; } });
  clear.addEventListener('click', () => { inp.value = ''; upd(); inp.focus(); });
  document.title = 'Комплексная логика — задачник';
}

// ---------- задачи ----------
const CHEV = '<svg class="chev" width="10" height="10" viewBox="0 0 10 10" aria-hidden="true"><path d="M3.5 2l3 3-3 3" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';
function reveal(t, ka, ks) {
  const a = open.has(ka), s = open.has(ks);
  const b = (k, on, label) => `<button type="button" class="rv${on ? ' on' : ''}" data-act="open" data-k="${esc(k)}" aria-expanded="${on}">${CHEV}${label}</button>`;
  return `<div class="reveal">${b(ka, a, 'Ответ')}${t.sol ? b(ks, s, 'Решение') : ''}</div>`
    + (a ? `<div class="rv-body ans-b rich">${t.ans}</div>` : '')
    + (s && t.sol ? `<div class="rv-body sol-b rich">${t.sol}</div>` : '');
}
function taskHtml(t, under, key) {
  const ok = !!(key && S.r[key] && S.r[key][t.id]);
  const btn = key ? `<button type="button" class="solved${ok ? ' on' : ''}" data-act="solve" data-key="${key}" data-id="${esc(t.id)}" aria-pressed="${ok}" aria-label="Задача ${t.n} решена" title="${ok ? 'Снять отметку' : 'Отметить задачу решённой'}">${ok ? '✓' : ''}</button>` : '';
  let h = `<article class="box" id="t${t.n}"><div class="task-row"><b class="num${ok ? ' ok' : ''}">${t.n}.</b><div class="rich">${t.cond}</div>${btn}</div>`;
  if (under) {
    h += reveal(t, 'a:' + key + t.id, 's:' + key + t.id);
  }
  return h + '</article>';
}
function answersBlock(tasks, withRepeat) {
  const rows = tasks.map((t) => `<tr><td>${t.n}</td><td><div class="rich">${t.ans}</div></td>${withRepeat ? `<td>${repeatLink(t.repeat)}</td>` : ''}</tr>`).join('');
  const sols = tasks.filter((t) => t.sol).map((t) => `<div class="solrow"><b>${t.n}.</b><div class="rich">${t.sol}</div></div>`).join('');
  return `<details><summary>${withRepeat ? 'Ответы и что повторить при ошибке' : 'Ответы — таблица, ' + tasks.length}</summary><div class="in"><div class="tw"><table>
      <thead><tr><th scope="col">№</th><th scope="col">Ответ</th>${withRepeat ? '<th scope="col">Что повторить при ошибке</th>' : ''}</tr></thead><tbody>${rows}</tbody></table></div></div></details>
    <details><summary>Решения, ${tasks.filter((t) => t.sol).length}</summary><div class="in">${sols}</div></details>`;
}
function repeatLink(r) {
  if (!r) return '';
  const s = r.sessions && r.sessions[0];
  return `${s ? `<a href="#/z/${s}" style="text-decoration:underline;text-underline-offset:3px">${r.title}</a>` : r.title}<span class="muted small"> · ${esc(r.pages)}${r.sessions && r.sessions.length ? ' · ' + sessionsWord(r.sessions) : ''}</span>`;
}

// ---------- занятие ----------
const CHK = '<svg width="12" height="12" viewBox="0 0 12 12" aria-hidden="true"><path d="M2.5 6.2l2.2 2.2 4.8-5" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"/></svg>';
const donePill = (act, n, on, label) => `<button type="button" class="pill${on ? ' on' : ''}" data-act="${act}" data-n="${n}" aria-pressed="${on}"><span class="pill-c">${on ? CHK : ''}</span>${label}</button>`;
async function viewZ(num) {
  const s = IDX.sessions.find((x) => x.num === num);
  if (!s) return notFound();
  const z = await get(`z/${pad(num)}.json`);
  if (route.page !== 'z' || route.n !== num) return;
  const under = S.mode === 'under', key = 'z' + num;
  const prev = IDX.sessions.find((x) => x.num === num - 1), next = IDX.sessions.find((x) => x.num === num + 1);
  const tests = testBefore(num), konts = kontrolAfter(num);
  const readItem = (r, i) => {
    let w = r.whereH, cont = false;
    if (w.endsWith(' (продолжение)')) { w = w.slice(0, -14); cont = true; }
    const cut = w.indexOf(', § ');
    const ch = cut > 0 ? w.slice(0, cut) : '', par = cut > 0 ? w.slice(cut + 2) : w;
    return `<li class="read-i"><span class="read-n">${i + 1}</span><div class="read-b">${ch ? `<span class="read-ch">${ch}</span>` : ''}
      <span class="read-p">${par}${cont ? ' <span class="cont">продолжение</span>' : ''}</span></div>
      <div class="read-pg"><span class="pg">${esc(r.pages)}</span>${r.pdf ? `<span class="pdf">${esc(r.pdf)}</span>` : ''}</div></li>`;
  };
  const BOOK = '<svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 19.5V5a2 2 0 0 1 2-2h13v16H6a2 2 0 0 0-2 2z"/><path d="M8 7h7"/></svg>';
  const LOOP = '<svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 12a9 9 0 0 1 15.5-6.3L21 8"/><path d="M21 3v5h-5"/><path d="M21 12a9 9 0 0 1-15.5 6.3L3 16"/><path d="M3 21v-5h5"/></svg>';
  const reading = z.reading.length
    ? `<ol class="read-list">${z.reading.map(readItem).join('')}</ol>`
    : '<p class="muted">Нового чтения нет: занятие целиком повторительное.</p>';
  const bookSrc = z.reading.length ? `<span class="book-src">${BOOK}${z.book1970 ? 'А. А. Зиновьев · <i>Комплексная логика</i> · 1970' : 'страницы книг; PDF — где есть скан'}</span>` : '';
  const review = z.review.length ? `<div class="review-note">${LOOP}<span>Повторение без нового чтения: ${z.review.join('; ')}</span></div>` : '';
  const examples = z.examples.map((e, j) => {
    const k = 'e:' + e.id;
    return `<div class="box ex"><div class="rich"><p><b>Пример ${j + 1}.</b></p>${e.cond}</div>
      ${reveal(e, 'a:' + k, 's:' + k)}</div>`;
  }).join('');
  const solvedN = z.tasks.filter((t) => S.r[key] && S.r[key][t.id]).length;
  const d = doneZ(num);
  $('#view').innerHTML = `
    <section class="card hero">
      <div class="hero-top">
        <div class="tags"><span class="tag">Занятие ${num}</span><span class="tag">Неделя ${s.week}</span><a class="tag tag-link" href="#/m/${s.module + 1}">Модуль ${ROM(s.module)} · ${esc(modTitle(s.module))}</a></div>
        ${donePill('doneZ', num, d, d ? 'Выполнено' : 'Отметить выполненным')}
      </div>
      <h1 class="hero-h">${z.topicH}</h1>
      <div class="hero-stats"><span>${z.tasks.length} ${plural(z.tasks.length, 'задача', 'задачи', 'задач')}</span><span class="dot"></span><span>${z.examples.length ? z.examples.length + ' ' + plural(z.examples.length, 'пример', 'примера', 'примеров') : 'без примеров'}</span><span class="dot"></span><span class="${solvedN ? 'ok' : ''}">решено ${solvedN} из ${z.tasks.length}</span>
        <span class="hero-bar"><span style="width:${Math.round(100 * solvedN / Math.max(1, z.tasks.length))}%"></span></span></div>
      ${tests.length || konts.length ? `<div class="hero-links">${tests.map((t) => `<a class="btn gold sm" href="#/t/${t.chapter}">Перед занятием — входной тест к ${testShort(t)}</a>`).join('')}${konts.map((k) => `<a class="btn gold sm" href="#/k/${k.k}">После занятия — контрольная работа ${k.k}</a>`).join('')}</div>` : ''}
      <div class="pn">
        ${prev ? `<a class="pn-a" href="#/z/${prev.num}"><span class="pn-k">‹ Занятие ${prev.num}</span><span class="pn-t">${prev.topicH}</span></a>` : '<span></span>'}
        ${next ? `<a class="pn-a r" href="#/z/${next.num}"><span class="pn-k">Занятие ${next.num} ›</span><span class="pn-t">${next.topicH}</span></a>` : '<span></span>'}
      </div>
    </section>
    <section class="card"><div class="row-between"><h2 class="eyebrow">Что прочитать</h2>${bookSrc}</div>${reading}${review}</section>
    ${z.examples.length ? `<section class="card"><h2 class="eyebrow">Примеры решений</h2>${examples}</section>` : ''}
    <section class="card">
      <div class="row-between"><h2 class="eyebrow">Задачи · ${z.tasks.length}${solvedN ? ` · решено ${solvedN}` : ''}</h2>
        <div role="group" aria-label="Где показывать ответы" style="display:flex;align-items:center;gap:8px"><span class="small muted">Ответы</span>
          <div class="seg"><button type="button" data-act="mode" data-m="end" class="${under ? '' : 'on'}">В конце</button><button type="button" data-act="mode" data-m="under" class="${under ? 'on' : ''}">Под задачей</button></div></div></div>
      ${z.tasks.map((t) => taskHtml(t, under, key)).join('')}
    </section>
    ${under ? '' : `<section class="card"><h2 class="eyebrow">Ответы и решения</h2><p class="muted small">Свёрнуты: откройте после своего решения.</p>${answersBlock(z.tasks, false)}</section>`}
    <nav class="foot-nav" aria-label="Соседние занятия">
      ${prev ? `<a class="foot-a" href="#/z/${prev.num}">‹ Занятие ${prev.num}</a>` : '<span></span>'}
      ${donePill('doneZ', num, d, d ? 'Занятие выполнено' : 'Отметить занятие выполненным')}
      ${next ? `<a class="foot-a" href="#/z/${next.num}">Занятие ${next.num} ›</a>` : '<span></span>'}</nav>`;
  document.title = `Занятие ${num} — Комплексная логика`;
}

// ---------- модуль ----------
function viewMod(m) {
  const mod = IDX.modules[m];
  if (!mod) return notFound();
  const ss = modSessions(m), nums = ss.map((s) => s.num), weeks = ss.map((s) => s.week);
  if (!ss.length) {
    $('#view').innerHTML = `<section class="card"><p class="eyebrow">Модуль ${ROM(m)}</p><h1>${esc(modTitle(m))}</h1>
      <p><b>К концу модуля:</b> ${esc(mod.goal)}</p><p class="muted">Занятия этого модуля готовятся и появятся здесь, как только будут написаны задачи.</p></section>`;
    document.title = `Модуль ${ROM(m)} — Комплексная логика`;
    return;
  }
  const d = ss.filter((s) => doneZ(s.num)).length;
  const rows = [];
  for (const s of ss) {
    for (const t of testBefore(s.num)) rows.push(`<a class="rowi gold${doneT(t.chapter) ? ' done' : ''}" href="#/t/${t.chapter}"><b>Т</b><span>Входной тест к ${testShort(t)}</span><span class="meta">${doneT(t.chapter) ? '<span class="ok">✓ выполнен</span>' : 'перед занятием ' + s.num}</span></a>`);
    rows.push(`<a class="rowi${doneZ(s.num) ? ' done' : ''}" href="#/z/${s.num}"><b>${s.num}</b><span>${s.topicH}</span><span class="meta">${doneZ(s.num) ? '<span class="ok">✓ выполнено</span>' : 'неделя ' + s.week}</span></a>`);
    for (const k of kontrolAfter(s.num)) rows.push(`<a class="rowi gold${doneK(k.k) ? ' done' : ''}" href="#/k/${k.k}"><b>К</b><span>Контрольная работа ${k.k}</span><span class="meta">${doneK(k.k) ? '<span class="ok">✓ выполнена</span>' : 'после занятия ' + s.num}</span></a>`);
  }
  const chs = mod.chapters.map((c) => (c === 0 ? 'Введение' : c === 16 ? 'раздел 16' : 'гл. ' + c)).join(', ');
  $('#view').innerHTML = `
    <section class="card"><p class="eyebrow">Модуль ${ROM(m)} · занятия ${Math.min(...nums)}–${Math.max(...nums)} · недели ${Math.min(...weeks)}–${Math.max(...weeks)}</p>
      <h1>${esc(modTitle(m))}</h1><p class="muted">Материал: ${chs}.</p>
      <p><b>К концу модуля:</b> ${esc(mod.goal)}</p>
      <div class="progress"><p>Выполнено занятий: <b>${d} из ${ss.length}</b></p><span class="bar"><span style="width:${Math.round(100 * d / ss.length)}%"></span></span></div></section>
    <section class="card"><h2 class="eyebrow">Занятия и проверки</h2><div class="rows">${rows.join('')}</div></section>
    <section class="card"><div class="navrow">${m > 0 ? `<a class="btn" href="#/m/${m}">‹ Модуль ${ROM(m - 1)}</a>` : '<span></span>'}${m < IDX.modules.length - 1 ? `<a class="btn" href="#/m/${m + 2}">Модуль ${ROM(m + 1)} ›</a>` : '<span></span>'}</div></section>`;
  document.title = `Модуль ${ROM(m)} — Комплексная логика`;
}

// ---------- контрольные и входные тесты ----------
function viewKList() {
  const rows = IDX.kontrol.map((k) => `<a class="rowi gold${doneK(k.k) ? ' done' : ''}" href="#/k/${k.k}"><b>К${k.k}</b><span>${esc(k.label)}<span class="sub">после занятия ${k.after} · материал занятий ${k.from}–${k.after}</span></span><span class="meta">${doneK(k.k) ? '<span class="ok">✓ выполнена</span>' : 'неделя ' + k.week}</span></a>`).join('');
  $('#view').innerHTML = `<header class="head"><h1>Контрольные</h1><p>Раз в месяц, после каждых восьми занятий: 30 новых задач, которых нет в занятиях; 3 часа.</p></header>
    <section class="card"><h2 class="eyebrow">${IDX.kontrol.length} работ</h2><div class="rows">${rows}</div></section>`;
  document.title = 'Контрольные — Комплексная логика';
}
function viewTList() {
  const rows = IDX.tests.map((t) => `<a class="rowi gold${doneT(t.chapter) ? ' done' : ''}" href="#/t/${t.chapter}"><b>Т</b><span>${t.titleH}<span class="sub">проверяет § ${t.sections.join('; ')}</span></span><span class="meta">${doneT(t.chapter) ? '<span class="ok">✓ выполнен</span><br>' : ''}перед занятием ${t.before}</span></a>`).join('');
  $('#view').innerHTML = `<header class="head"><h1>Входные тесты</h1><p>Перед каждой главой: 8–10 задач на то, что глава берёт из прежних. Не сдан — таблица ответов покажет, какие параграфы повторить.</p></header>
    <section class="card"><h2 class="eyebrow">${IDX.tests.length} тестов</h2><div class="rows">${rows}</div></section>`;
  document.title = 'Входные тесты — Комплексная логика';
}
function checkedList(tasks) {
  const seen = new Map();
  for (const t of tasks) if (t.repeat && !seen.has(t.repeat.section)) seen.set(t.repeat.section, t.repeat);
  return [...seen.values()].sort((a, b) => a.section.localeCompare(b.section))
    .map((r) => `<li>${r.title}, ${esc(r.pages)}${r.sessions && r.sessions.length ? ` — <a href="#/z/${r.sessions[0]}" style="text-decoration:underline;text-underline-offset:3px">${sessionsWord(r.sessions)}</a>` : ''}</li>`).join('');
}
async function viewCheck(kind, id) {
  const meta = kind === 'k' ? IDX.kontrol.find((k) => k.k === id) : IDX.tests.find((t) => t.chapter === id);
  if (!meta) return notFound();
  const data = await get(`${kind}/${pad(id)}.json`);
  if (route.page !== kind || route.n !== id) return;
  const d = kind === 'k' ? doneK(id) : doneT(id);
  const tasks = data.tasks.map((t) => `<article class="box" id="t${t.n}"><div class="task-row"><b class="num">${t.n}.</b><div class="rich">${t.cond}</div></div></article>`).join('');
  const head = kind === 'k'
    ? `<p class="eyebrow gold">Контрольная работа ${id} · неделя ${meta.week}</p><h1>${esc(meta.label)}</h1>
       <p class="muted">После занятия ${meta.after} · материал занятий ${meta.from}–${meta.after} · ${data.tasks.length} задач · время — <b style="color:var(--text)">${esc(data.time)}</b> · книгой и записями пользоваться можно</p>`
    : `<p class="eyebrow gold">Входной тест · перед занятием ${meta.before} · неделя ${meta.week}</p><h1>${testTo(meta)}</h1>
       <p class="muted">${data.tasks.length} ${plural(data.tasks.length, 'задача', 'задачи', 'задач')} на то, что глава берёт из прежних · время — <b style="color:var(--text)">${esc(data.time)}</b> · без книги и записей</p>`;
  const back = kind === 'k' ? '<a class="foot-a" href="#/k">‹ Все контрольные</a>' : '<a class="foot-a" href="#/t">‹ Все входные тесты</a>';
  const doneL = kind === 'k' ? (d ? '✓ Работа выполнена' : 'Отметить работу выполненной') : (d ? '✓ Тест выполнен' : 'Отметить тест выполненным');
  const go = kind === 't' ? `<a class="foot-a" href="#/z/${meta.before}">К занятию ${meta.before} ›</a>` : '';
  $('#view').innerHTML = `
    <section class="card gold">${head}<div class="navrow">${back}<span class="mid">${go}</span>${donePill('done' + kind.toUpperCase(), id, d, doneL.replace('✓ ', ''))}</div></section>
    <section class="card"><h2 class="eyebrow">Как оценивать</h2><p>${esc(data.pass)}</p></section>
    <section class="card"><h2 class="eyebrow">Что проверяется</h2><ul class="plain-list">${checkedList(data.tasks)}</ul></section>
    <section class="card"><h2 class="eyebrow">Задачи</h2>${tasks}</section>
    <section class="card"><h2 class="eyebrow">Ответы и решения</h2><p class="muted small">Свёрнуты: откройте после того, как решите всю работу.</p>${answersBlock(data.tasks, true)}</section>`;
  document.title = (kind === 'k' ? `Контрольная ${id}` : `Входной тест к ${testShort(meta)}`) + ' — Комплексная логика';
}

// ---------- поиск, справка ----------
function viewPoisk(q) {
  $('#view').innerHTML = `<header class="head"><h1>Поиск</h1><p>По номеру занятия (76) и по словам из его названия (кванторы, S<span class="ss"><sup>e</sup><sub>n</sub></span>, координаты).</p></header>
    <section class="card"><label for="p-q" class="eyebrow">Запрос</label>
      <div class="field">${searchIcon(18)}<input id="p-q" type="search" autocomplete="off" value="${esc(q)}"></div>
      <p class="small muted" id="p-head" style="margin:0"></p><div class="results" id="p-list"></div></section>`;
  const inp = $('#p-q');
  const upd = () => {
    const f = findSessions(inp.value);
    $('#p-head').textContent = !inp.value.trim() ? 'Введите номер или слово.' : f.length ? 'Найдено ' + plural(f.length, 'занятие', 'занятия', 'занятий') + ': ' + f.length : 'Ничего не найдено.';
    $('#p-list').innerHTML = resultsHtml(f, 90);
    history.replaceState(null, '', '#/poisk/' + encodeURIComponent(inp.value.trim()));
  };
  inp.addEventListener('input', upd);
  upd();
  inp.focus();
  document.title = 'Поиск — Комплексная логика';
}
async function viewOboz() {
  const sp = await get('spravka.json');
  if (route.page !== 'oboz') return;
  $('#view').innerHTML = `<header class="head"><h1>Обозначения</h1><p>Символы книги (Введение, § 3–8, с. 4–12) и как они читаются.</p></header>`
    + sp.oboznacheniya.map((s) => `<section class="card"><h2 class="eyebrow">${s.title}</h2><div class="rich">${s.html}</div></section>`).join('');
  document.title = 'Обозначения — Комплексная логика';
}
async function viewUstr() {
  const sp = await get('spravka.json');
  if (route.page !== 'ustr') return;
  const lv = Object.entries(sp.levels).map(([k, v]) => `<div class="stepi"><b>${k}</b><b>${esc(v.name)}</b><span>${esc(v.short)}</span></div>`).join('');
  const ty = Object.entries(sp.types).map(([k, v]) => `<div class="stepi"><b>${k}</b><b>${esc(v)}</b><span>${k === 'E' ? 'около четверти задач: найти ошибку и назвать нарушенное правило с номером и страницей' : ''}</span></div>`).join('');
  const st = Object.entries(sp.steps).filter(([k]) => k !== 'mixed').map(([, v], i) => `<div class="stepi"><b>${i + 1}</b><b>${esc(v.split(' (')[0])}</b><span>${esc((v.match(/\((.*)\)/) || ['', ''])[1])}</span></div>`).join('');
  $('#view').innerHTML = `<header class="head"><h1>Как устроены задачи</h1><p>Задачи идут от простого к сложному; около четверти — диагностика: найти, что не так, и назвать нарушенное правило.</p></header>
    <section class="card"><h2 class="eyebrow">Десять ступеней</h2><div class="steps">${lv}</div></section>
    <section class="card"><h2 class="eyebrow">Лестница в параграфе</h2><p class="muted">Задачи параграфа идут в таком порядке; в конце занятия — плановое повторение прошлых параграфов.</p><div class="steps">${st}</div></section>
    <section class="card"><h2 class="eyebrow">Типы задач</h2><div class="steps">${ty}</div></section>
    <section class="card"><h2 class="eyebrow">Решения</h2><p>Каждое решение ссылается на определения, аксиомы, правила и страницу книги. Ответы и решения свёрнуты: их можно показывать в конце занятия или под каждой задачей.</p></section>`;
  document.title = 'Как устроены задачи — Комплексная логика';
}
function notFound() {
  $('#view').innerHTML = `<section class="card"><h1>Страница не найдена</h1><p><a class="btn" href="#/">К курсу</a></p></section>`;
}


// ---------- плавающее оглавление задач справа (как в Notion) ----------
let tocScroll = null;
function buildToc() {
  const old = document.getElementById('ntoc');
  if (old) old.remove();
  if (tocScroll) { window.removeEventListener('scroll', tocScroll); tocScroll = null; }
  const arts = [...document.querySelectorAll('#view article[id^="t"]')];
  if (arts.length < 2) return;
  const solved = (a) => !!a.querySelector('.solved.on');
  const label = (a) => {
    const n = a.querySelector('.num').textContent.trim();
    const p = a.querySelector('.rich');
    const tmp = document.createElement('div');
    tmp.innerHTML = p ? p.innerHTML.replace(/<br\s*\/?>|<\/p>|<\/td>|<\/th>/g, ' ') : '';
    let txt = tmp.textContent.replace(/\s+/g, ' ').trim();
    // обозначения в начале условия («Буквы x, y — высказывания; ….») в оглавлении пропускаем
    const m = txt.match(/^(Буквы|Обозначения|Здесь|Пусть)(?=[\s:]).*?[.;:]\s+(?=[А-ЯЁ«])/);
    if (m && m[0].length < txt.length - 10) txt = txt.slice(m[0].length);
    return { n, txt };
  };
  const box = document.createElement('div');
  box.id = 'ntoc';
  box.className = 'ntoc';
  box.setAttribute('aria-label', 'Задачи');
  box.innerHTML = `<div class="ntoc-dashes">${arts.map((a, i) => `<div class="ntoc-d" data-i="${i}"><div class="${solved(a) ? 'ok' : ''}"></div></div>`).join('')}</div>
    <div class="ntoc-panel" role="navigation"><div class="ntoc-list">${arts.map((a, i) => {
      const l = label(a);
      return `<a class="ntoc-i${solved(a) ? ' ok' : ''}" href="#${a.id}" data-i="${i}"><span class="ntoc-n">${l.n}</span>${esc(l.txt)}</a>`;
    }).join('')}</div></div>`;
  document.body.appendChild(box);
  const dashes = [...box.querySelectorAll('.ntoc-d')], items = [...box.querySelectorAll('.ntoc-i')];
  const dashCol = box.querySelector('.ntoc-dashes'), list = box.querySelector('.ntoc-list');
  box.addEventListener('click', (e) => {
    const el = e.target.closest('[data-i]');
    if (!el) return;
    e.preventDefault();
    arts[+el.dataset.i].scrollIntoView({ behavior: 'smooth', block: 'start' });
  });
  let cur = -1;
  tocScroll = () => {
    const line = window.innerHeight * 0.3;
    let k = 0;
    arts.forEach((a, i) => { if (a.getBoundingClientRect().top <= line) k = i; });
    if (k === cur) return;
    cur = k;
    dashes.forEach((d, i) => d.classList.toggle('on', i === k));
    items.forEach((d, i) => d.classList.toggle('on', i === k));
    const d = dashes[k];
    if (d) dashCol.scrollTop = Math.max(0, d.offsetTop - dashCol.clientHeight / 2);
    const it = items[k];
    if (it && !box.matches(':hover')) list.scrollTop = Math.max(0, it.offsetTop - list.clientHeight / 2);
  };
  window.addEventListener('scroll', tocScroll, { passive: true });
  tocScroll();
}

// ---------- события ----------
document.addEventListener('click', (e) => {
  const b = e.target.closest('[data-act]');
  if (!b) return;
  const act = b.dataset.act, n = +b.dataset.n;
  if (act === 'side') { S.side = !S.side; save(); renderSide(); return; }
  if (act === 'open') { const k = b.dataset.k; open.has(k) ? open.delete(k) : open.add(k); rerender(); return; }
  if (act === 'mode') { S.mode = b.dataset.m; save(); rerender(); return; }
  if (act === 'solve') {
    const key = b.dataset.key, id = b.dataset.id;
    S.r[key] = S.r[key] || {};
    if (S.r[key][id]) delete S.r[key][id]; else S.r[key][id] = 1;
    save(); rerender(); return;
  }
  if (act === 'doneZ' || act === 'doneK' || act === 'doneT') {
    const box = { doneZ: S.z, doneK: S.k, doneT: S.t }[act];
    if (box[n]) delete box[n]; else box[n] = 1;
    save(); rerender(true);
  }
});

function parse() {
  const p = location.hash.replace(/^#\/?/, '').split('/');
  const n = parseInt(p[1], 10);
  switch (p[0]) {
    case '': return { page: 'kurs' };
    case 'z': return { page: 'z', n, mod: (IDX.sessions.find((s) => s.num === n) || {}).module };
    case 'm': return { page: 'mod', m: n - 1 };
    case 'k': return isNaN(n) ? { page: 'kontr' } : { page: 'k', n };
    case 't': return isNaN(n) ? { page: 'vhod' } : { page: 't', n };
    case 'poisk': return { page: 'poisk', q: decodeURIComponent(p.slice(1).join('/') || '') };
    case 'oboz': return { page: 'oboz' };
    case 'ustr': return { page: 'ustr' };
    default: return { page: 'none' };
  }
}
async function show() {
  try {
    switch (route.page) {
      case 'kurs': return viewKurs();
      case 'z': return await viewZ(route.n);
      case 'mod': return viewMod(route.m);
      case 'kontr': return viewKList();
      case 'vhod': return viewTList();
      case 'k': return await viewCheck('k', route.n);
      case 't': return await viewCheck('t', route.n);
      case 'poisk': return viewPoisk(route.q);
      case 'oboz': return await viewOboz();
      case 'ustr': return await viewUstr();
      default: return notFound();
    }
  } catch (err) {
    $('#view').innerHTML = `<section class="card"><h1>Не удалось загрузить данные</h1><p class="muted">${esc(err.message)}. Проверьте подключение к сети и обновите страницу.</p></section>`;
  }
}
async function rerender(side) {
  const y = window.scrollY;
  await show();
  buildToc();
  if (side) renderSide();
  window.scrollTo(0, y);
}
async function onHash() {
  route = parse();
  renderSide();
  await show();
  window.scrollTo(0, 0);
  buildToc();
}

(async function start() {
  try {
    IDX = await get('index.json');
  } catch (err) {
    $('#view').innerHTML = `<section class="card"><h1>Не удалось загрузить данные</h1><p class="muted">Сайт открывают через веб-сервер (GitHub Pages или <code>python3 -m http.server</code> в корне репозитория), а не как файл.</p></section>`;
    return;
  }
  window.addEventListener('hashchange', onHash);
  onHash();
})();
