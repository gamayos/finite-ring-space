/* register.js — the Filters (papers × blocks × statuses) of the register and of the Ledger, Predictions and Explicability tabs.
   On register.html the rows come from register-data.js (the records of register.json and the rows' rendered cells, a script: the
   page opens from a local file too). On a tab the rows are the page's own and a choice it can show is shown in place; a choice it
   cannot show opens the tab, or the register view, that can. The counts come from register-index.js: every row's paper, block and
   status, and the restatements the Predictions and Explicability tabs fold into their first appearance. No framework. */
(function () {
  "use strict";
  var BLOCKS = {X: "Explanation", P: "Prediction", Z: "Horizon", T: "Task", Y: "Hypothesis"}, BLOCK_ORDER = ["X", "P", "Z", "T", "Y"];
  var FORCED_TAG = {X: "T", P: "T", T: "O", Y: "O"};                       /* the rule: choosing X or P sets the status to theorem (Q23), T or Y to open */
  var TAGS = {G: "ground", P: "pillar", T: "theorem", D: "definition", R: "realisation", I: "import", "Ω": "Ω-hard", O: "open"};
  var TABS = ["ledger", "pred", "expl"], FILE = {ledger: "00-ledger.html", pred: "predictions.html", expl: "explicability.html"};
  var HAS = {ledger: function (s) { return s.paper === "00"; },             /* what a tab shows in place: the master's rows on the Ledger, */
             pred: function (s) { return s.block === "P"; },                /* the predictions, a restatement folded into its first appearance, by source paper */
             expl: function (s) { return s.block === "X"; }};               /* and the explanations, folded the same way */
  var OPENS = {ledger: HAS.ledger,                                          /* what opens a tab from elsewhere: a paper's own predictions or explanations, */
               pred: function (s) { return s.block === "P" && s.paper === "all"; },   /* restatements included, stay on the register */
               expl: function (s) { return s.block === "X" && s.paper === "all"; }};
  var PAGE = window.FRC_PAGE || null;                                       /* the tab in view; none on register.html */
  var IDX = window.FRC_INDEX || {papers: [], rows: [], folded: []}, FOLD = {};
  IDX.folded.forEach(function (k) { FOLD[k] = true; });
  function tabOf(s) { if (PAGE && HAS[PAGE](s)) return PAGE; for (var i = 0; i < TABS.length; i++) if (OPENS[TABS[i]](s)) return TABS[i]; return null; }
  function esc(s) { return String(s).replace(/[&<>"']/g, function (c) { return "&#" + c.charCodeAt(0) + ";"; }); }
  function tagsOf(r) { return r.tag.split("|"); }
  function copy(s) { return {paper: s.paper, block: s.block, tag: s.tag, q: s.q}; }
  function setBlock(s, b) { s.block = b; if (FORCED_TAG[b]) s.tag = FORCED_TAG[b]; return s; }
  function noView(s) { return s.paper === "all" && s.block === "all" && s.tag === "all"; }   /* the rule: all papers, all blocks and every status is no view; one status is (14 October 2026) */
  /* the three choices, each a function of the selection: the selection it yields */
  function pickPaper(s, k) { s = copy(s); s.paper = (s.paper === k && k !== "all") ? "all" : k; if (noView(s)) s.tag = "O"; return s; }                              /* then every paper: every block's open rows (14 October 2026) */
  function pickBlock(s, k) { s = copy(s); if (k === "all" || s.block === k) { s.block = "all"; if (noView(s)) s.paper = "00"; } else setBlock(s, k); return s; }   /* then every block: the master */
  function pickTag(s, k) { s = copy(s); s.tag = (s.tag === k && k !== "all") ? "all" : k; if (noView(s)) s.paper = "00"; return s; }                                  /* then every status: the master */
  /* the rows a selection shows: on Predictions and Explicability a restatement is folded into its first appearance */
  function shows(s, r, tab) {
    if (s.paper !== "all" && r.paper !== s.paper) return false;
    if (s.block !== "all" && r.block !== s.block) return false;
    if (s.tag !== "all" && tagsOf(r).indexOf(s.tag) < 0) return false;
    return !((tab === "pred" || tab === "expl") && FOLD[r.rid]);
  }
  var recs = [];                                                            /* the rows counted: the index on a tab; the records, with their text, on the register */
  function count(s) { var tab = tabOf(s), n = 0; recs.forEach(function (r) { if (shows(s, r, tab) && (!s.q || !r._t || r._t.indexOf(s.q) >= 0)) n++; }); return n; }
  function href(s) {                                                        /* the address of a selection: the tab that shows it, else the register */
    var tab = tabOf(s), u = new URLSearchParams();
    if (s.paper !== "all" && tab !== "ledger") u.set("paper", s.paper);
    if (s.block !== "all" && (tab === "ledger" || !tab)) u.set("block", s.block);
    if (s.tag !== (FORCED_TAG[s.block] || "all")) u.set("tag", s.tag);
    if (s.q) u.set("q", s.q);
    return (tab ? FILE[tab] : "register.html") + (u.toString() ? "?" + u.toString() : "");
  }
  /* the selection: the tab's own, then the address */
  var qs = new URLSearchParams(location.search);
  var st = {paper: PAGE === "ledger" ? "00" : "all", block: PAGE === "pred" ? "P" : (PAGE === "expl" ? "X" : "all"), tag: "all", q: ""};
  ["paper", "block", "tag", "q"].forEach(function (k) { if (qs.has(k)) st[k] = qs.get(k); });
  if (!qs.has("tag")) st.tag = FORCED_TAG[st.block] || "all";              /* the status the block implies, unless the address says otherwise */
  if (noView(st)) st.tag = "O";                                             /* an address with no view: every block's open rows (14 October 2026) */
  st.q = st.q.trim().toLowerCase();
  var tbody = document.getElementById("rows"), count_ = document.getElementById("count"), empty = document.getElementById("empty"), q = document.getElementById("q");
  q.value = st.q;
  var waiting = null;
  function withData(then) {                                                 /* register-data.js, loaded once, when a view needs it */
    if (window.FRC_REGISTER) { then(); return; }
    if (waiting) { waiting.push(then); return; }
    waiting = [then]; var sc = document.createElement("script"); sc.src = "register-data.js";
    sc.onload = function () { var w = waiting; waiting = []; w.forEach(function (f) { f(); }); }; document.head.appendChild(sc);
  }
  function pill(box, label, dot, next, active) {
    var n = count(active ? st : next);
    var b = document.createElement("button"); b.type = "button"; b.setAttribute("aria-pressed", String(active));
    b.innerHTML = (dot ? '<span class="dot ' + dot + '"></span>' : "") + label + ' <span class="n">' + n + "</span>";
    b.addEventListener("click", function () { go(next); }); box.appendChild(b);
  }
  var KEEP = "frc-filters-open";                                            /* the Filters stay open across a pill that opens another page (14 October 2026) */
  function keepOpen() { try { if (document.getElementById("filters").open) sessionStorage.setItem(KEEP, "1"); } catch (e) {} }
  function restoreOpen() { try { if (sessionStorage.getItem(KEEP)) { sessionStorage.removeItem(KEEP); document.getElementById("filters").open = true; } } catch (e) {} }
  function go(s) { if (tabOf(s) !== PAGE) { keepOpen(); location.href = href(s); return; } st = s; update(); }
  var allTags = {};
  function build() {
    var pb = document.getElementById("papers"), bb = document.getElementById("blocks"), tb = document.getElementById("tags");
    pb.innerHTML = '<span class="cap">Papers</span>'; bb.innerHTML = '<span class="cap">Blocks</span>'; tb.innerHTML = '<span class="cap">Status</span>';
    pill(pb, "All", "", pickPaper(st, "all"), st.paper === "all");
    IDX.papers.forEach(function (p) { var k = p[0]; pill(pb, k === "00" ? "00 master" : k, "", pickPaper(st, k), st.paper === k); });
    pill(bb, "All", "", pickBlock(st, "all"), st.block === "all");
    BLOCK_ORDER.forEach(function (k) { pill(bb, k + ": " + BLOCKS[k], "", pickBlock(st, k), st.block === k); });
    pill(tb, "All", "", pickTag(st, "all"), st.tag === "all");
    Object.keys(TAGS).forEach(function (k) { if (allTags[k]) pill(tb, TAGS[k], "dot t-" + (k === "Ω" ? "om" : k.toLowerCase()), pickTag(st, k), st.tag === k); });
    /* the collapsed filters: the selection in one line (the address's values escaped) */
    function cap(c, v) { return '<span class="grp"><span class="cap">' + c + "</span>" + v + "</span>"; }
    var pv = st.paper === "all" ? "All" : (st.paper === "00" ? "00 master" : esc(st.paper)), bv = st.block === "all" ? "All" : esc(BLOCKS[st.block] ? st.block + ": " + BLOCKS[st.block] : st.block),
        tv = st.tag === "all" ? "All" : '<span class="dot t-' + esc(st.tag === "Ω" ? "om" : st.tag.toLowerCase()) + '"></span>' + esc(TAGS[st.tag] || st.tag);
    document.getElementById("sel").innerHTML = [cap("Papers", pv), cap("Blocks", bv), cap("Status", tv)].join('<span class="sep">·</span>');
  }
  function update() {
    history.replaceState(null, "", href(st) + location.hash);
    build(); if (PAGE) renderTab(); else render();
  }
  q.addEventListener("input", function () { st.q = q.value.trim().toLowerCase(); update(); });
  function mark() { var k = location.hash.slice(1), t = k && document.getElementById(k); if (t) { var tr = t.closest("tr") || t; tr.classList.add("target"); return tr; } return null; }

  /* ---- a tab: the page's rows, filtered in place ---- */
  var trs = [], heads = [];
  function inPlace(tr) {
    var paper = PAGE === "ledger" ? "00" : tr.dataset.block, block = PAGE === "ledger" ? tr.dataset.block : (PAGE === "pred" ? "P" : "X");
    return (st.paper === "all" || paper === st.paper) && (st.block === "all" || block === st.block)
        && (st.tag === "all" || tr.dataset.tag.split("|").indexOf(st.tag) >= 0) && (!st.q || tr.textContent.toLowerCase().indexOf(st.q) >= 0);
  }
  function renderTab() {
    var shown = 0, vis = {};
    trs.forEach(function (tr) { var ok = inPlace(tr); tr.hidden = !ok; if (ok) { shown++; vis[tr.dataset.block] = true; } });
    heads.forEach(function (h) { h.hidden = !vis[h.dataset.block]; });
    count_.textContent = shown + " of " + trs.length; empty.hidden = shown > 0;
    corpusSearch();
  }
  /* the Ledger tab: the search also runs over every public paper ledger, the hits listed under the table as links to the predicates on their pages */
  var corpus = document.getElementById("corpus"), hits = document.getElementById("corpus-hits"), chead = document.getElementById("corpus-head");
  function corpusSearch() {
    if (!corpus) return;
    if (!st.q) { corpus.hidden = true; return; }
    withData(function () {
      if (!st.q) { corpus.hidden = true; return; }
      var found = window.FRC_REGISTER.rows.filter(function (r) { return r.paper !== "00" && (r.no + ":" + r.label + " " + (r.key || "") + " " + r.tag + " " + r.paper + " " + r.text).toLowerCase().indexOf(st.q) >= 0; });
      hits.innerHTML = "";
      found.slice(0, 200).forEach(function (r) {
        var li = document.createElement("li"), a = document.createElement("a"), tg = document.createElement("span"), sn = document.createElement("span");
        a.className = "rowref"; a.href = r.page; a.title = r.key || ""; a.textContent = r.no + ":" + r.label;
        tg.className = "tag " + (r.tag === "Ω" ? "om" : r.tag.split("|")[0].toLowerCase()); tg.textContent = r.tag;
        var t = r.text; sn.className = "snip"; sn.textContent = t.length > 180 ? t.slice(0, 180).replace(/\s+\S*$/, "") + "…" : t;
        li.appendChild(a); li.appendChild(document.createTextNode(" ")); li.appendChild(tg); li.appendChild(document.createTextNode(" ")); li.appendChild(sn); hits.appendChild(li);
      });
      chead.textContent = found.length ? "In the papers' ledgers: " + found.length + (found.length === 1 ? " predicate" : " predicates") + (found.length > 200 ? " (the first 200 listed)" : "") : "In the papers' ledgers: nothing matches";
      corpus.hidden = false;
    });
  }

  /* ---- the register: the rows from register-data.js ---- */
  var reg = null, frags = null, papers = {};
  function text(r) { return (r.no + ":" + r.label + " " + (r.key || "") + " " + r.tag + " " + r.paper + " " + r.text).toLowerCase(); }
  function badge(tag) { return tag.split("|").map(function (t) { return '<span class="tag ' + (t === "Ω" ? "om" : t.toLowerCase()) + '" title="' + (TAGS[t] || t) + '">' + t + "</span>"; }).join(" "); }
  var observer = null;
  function typeset(nodes) { if (window.MathJax && MathJax.typesetPromise) MathJax.startup.promise.then(function () { return MathJax.typesetPromise(nodes); }); }
  function render() {
    var rows = reg.rows.filter(function (r) { return shows(st, r, null) && (!st.q || r._t.indexOf(st.q) >= 0); });
    tbody.innerHTML = ""; if (observer) observer.disconnect();
    var head = null, html = [], byPaper = st.paper === "all";
    rows.forEach(function (r) {
      var h = byPaper ? r.paper : r.block;
      if (h !== head) {
        head = h;
        var p = papers[r.paper], title = byPaper ? ((r.paper === "00" ? "00. " : r.no + ". ") + (p ? p.title : r.paper) + ' <a class="lnk" href="' + (p ? p.page : "#") + '" title="the ledger">¶</a>')
                                                : (r.block + ". " + ((p && p.blocks.filter(function (b) { return b.letter === r.block; })[0] || {}).title || BLOCKS[r.block] || ""));
        html.push('<tr class="blockhead"><td colspan="4"><b>' + title + "</b></td></tr>");
      }
      var f = frags.rows[r.rid] || frags.rows[r.key] || {statement: "", source: ""};
      html.push('<tr data-key="' + (r.key || "") + '"><td class="lab"><a href="' + r.page + '" title="the predicate in its ledger">' + (r.paper === "00" ? "00" : r.no) + ":" + r.label + '</a><span class="key" id="' + (r.key || "") + '">' + (r.key || "") + "</span></td>"
              + '<td class="pred">' + f.statement + '</td><td class="status">' + badge(r.tag) + '</td><td class="src">' + f.source + "</td></tr>");
    });
    tbody.innerHTML = html.join("");
    count_.textContent = rows.length + " of " + reg.rows.length; empty.hidden = rows.length > 0;
    /* typeset the first rows now, the rest as they scroll into view (60 at a time) */
    var trs = Array.prototype.slice.call(tbody.querySelectorAll("tr[data-key]"));
    trs.forEach(function (t) { t.dataset.ts = "0"; });
    function chunk(from) { var list = []; for (var i = from; i < trs.length && list.length < 60; i++) if (trs[i].dataset.ts === "0") { trs[i].dataset.ts = "1"; list.push(trs[i]); } if (list.length) typeset(list); }
    chunk(0);
    if ("IntersectionObserver" in window && trs.length > 60) {
      observer = new IntersectionObserver(function (es) { es.forEach(function (e) { if (e.isIntersecting && e.target.dataset.ts === "0") chunk(trs.indexOf(e.target)); }); }, {rootMargin: "600px 0px"});
      trs.forEach(function (t) { observer.observe(t); });
    }
    var row = mark(); if (row) row.scrollIntoView({block: "center"});
  }

  var key = /^#p\d{5}$/.test(location.hash) ? location.hash.slice(1) : null;
  if (PAGE) {
    IDX.rows.forEach(function (r) { recs.push({paper: r[0], block: r[1], tag: r[2], rid: r[3]}); r[2].split("|").forEach(function (t) { allTags[t] = true; }); });
    if (!HAS[PAGE](st)) { location.replace(href(st) + location.hash); return; }   /* an address this tab does not show */
    trs = Array.prototype.slice.call(document.querySelectorAll("#ledger tbody tr[data-tag]")); heads = Array.prototype.slice.call(document.querySelectorAll("#ledger tbody tr.blockhead"));
    restoreOpen(); update(); mark();
    if (key && !document.getElementById(key)) withData(function () {     /* a key this tab does not list: the register says whose, and the predicate opens on its page */
      var hit = window.FRC_REGISTER.rows.filter(function (r) { return r.key === key; })[0];
      if (hit) location.replace(hit.page);
      else if ((window.FRC_REGISTER.superseded || []).some(function (s) { return s.key === key; })) location.replace("register.html#" + key);   /* superseded (Q19) */
    });
  } else {
    if (!key && tabOf(st)) { location.replace(href(st)); return; }            /* a view a tab shows opens there */
    withData(function () {
      reg = window.FRC_REGISTER; frags = window.FRC_REGISTER_ROWS;
      reg.header.papers.forEach(function (p) { papers[p.key] = p; });
      reg.rows.forEach(function (r) { r._t = text(r); recs.push(r); tagsOf(r).forEach(function (t) { allTags[t] = true; }); });
      if (key) { var hits = reg.rows.filter(function (r) { return r.key === key; }), hit = hits.filter(function (r) { return r.no === parseInt(key.slice(1, 3), 10); })[0] || hits[0];   /* a shared key: the row of its ledger of origin (LM12) */
        if (hit) { st = {paper: hit.paper, block: "all", tag: "all", q: st.q};   /* every status: the key's row shows whatever its tag (MS1) */
          if (tabOf(st)) { location.replace(href(st) + location.hash); return; } }   /* a master key: the Ledger tab */
        else { var sup = (reg.superseded || []).filter(function (s) { return s.key === key; })[0];   /* a key that left: superseded, with its successors (Q19) */
          if (sup) { var note = document.createElement("p"); note.className = "note superseded"; note.id = key;
            var links = sup.successors.map(function (s) { var r = reg.rows.filter(function (x) { return x.key === s; }); r = r.filter(function (x) { return x.no === parseInt(s.slice(1, 3), 10); })[0] || r[0];
              return r ? '<a href="' + r.page + '"><code>' + s + '</code></a>' : "<code>" + s + "</code>"; });
            note.innerHTML = "<code>" + key + "</code> is superseded" + (links.length ? " by " + links.join(", ") : "") + ".";
            var tb = document.getElementById("ledger"); tb.parentNode.insertBefore(note, tb); } } }
      restoreOpen(); update();
      if (key) { var el = document.getElementById(key); if (el) el.scrollIntoView({block: "center"}); }   /* the key's row, or its superseded notice, in view (MS1) */
    });
  }
})();
