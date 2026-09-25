/* ledger.js — filter and search on a ledger page (master or paper). No framework. */
function initLedger(root) {
  "use strict";
  root = root || document;
  var table = root.querySelector("table.ledger"); if (!table) return;
  var rows = Array.prototype.slice.call(table.querySelectorAll("tbody tr[data-tag]"));
  var heads = Array.prototype.slice.call(table.querySelectorAll("tbody tr.blockhead"));
  var tally = root.querySelector(".tally"), q = root.querySelector("input[type=search]"), count = root.querySelector(".count"), empty = root.querySelector(".empty");
  var active = "all", query = "";
  var NAMES = {G:"ground", P:"pillar", T:"theorem", D:"definition", R:"realisation", I:"import", E:"prediction", "Ω":"Ω-hard", O:"open"};
  if (window.LEDGER_TAGS === "bypaper") {          /* the predictions page: the tally counts sources, not tags */
    NAMES = {};
    rows.forEach(function (r) { var t = r.dataset.tag; if (!NAMES[t]) NAMES[t] = (t === "00" ? "master" : t); });
  }
  function tagsOf(r) { return r.dataset.tag.split("|"); }
  function build() {
    var counts = {all: rows.length};
    rows.forEach(function (r) { tagsOf(r).forEach(function (t) { counts[t] = (counts[t] || 0) + 1; }); });
    tally.innerHTML = "";
    [["all", "All"]].concat(Object.keys(NAMES).map(function (k) { return [k, NAMES[k]]; })).forEach(function (d) {
      if (!counts[d[0]]) return;
      var b = document.createElement("button"); b.type = "button";
      b.setAttribute("aria-pressed", String(active === d[0]));
      b.innerHTML = '<span class="dot t-' + (window.LEDGER_TAGS === "bypaper" && d[0] !== "all" ? "e" : (d[0] === "Ω" ? "om" : d[0].toLowerCase())) + '"></span>' + d[1] + ' <span class="n">' + counts[d[0]] + "</span>";
      b.addEventListener("click", function () { active = (active === d[0] && d[0] !== "all") ? "all" : d[0]; build(); render(); });
      tally.appendChild(b);
    });
  }
  function render() {
    var shown = 0, visibleBlocks = {};
    rows.forEach(function (r) {
      var ok = (active === "all" || tagsOf(r).indexOf(active) >= 0) && (!query || r.textContent.toLowerCase().indexOf(query) >= 0);
      r.hidden = !ok; if (ok) { shown++; visibleBlocks[r.dataset.block] = true; }
    });
    heads.forEach(function (h) { h.hidden = !visibleBlocks[h.dataset.block]; });
    count.textContent = shown + " of " + rows.length; empty.hidden = shown > 0;
  }
  /* the corpus register (window.REGISTER_URL, the Ledger page): the query is also run over every public paper ledger, the hits listed under the table as links to the predicates on their pages */
  var corpus = root.querySelector("#corpus"), hits = root.querySelector("#corpus-hits"), chead = root.querySelector("#corpus-head"), reg = null, regLoading = false;
  function loadReg(then) {
    if (reg) { then(reg); return; }
    if (regLoading) return;
    regLoading = true;
    function fromScript() { var sc = document.createElement("script"); sc.src = "register-data.js"; sc.onload = function () { reg = window.FRC_REGISTER; then(reg); }; document.head.appendChild(sc); }   /* a local file: fetch() is refused, a script is not */
    if (location.protocol === "file:") { fromScript(); return; }
    fetch(window.REGISTER_URL).then(function (r) { return r.json(); }).then(function (d) { reg = d; then(reg); }).catch(fromScript);
  }
  function corpusSearch() {
    if (!corpus || !window.REGISTER_URL) return;
    if (!query) { corpus.hidden = true; return; }
    loadReg(function (d) {
      if (!query) { corpus.hidden = true; return; }
      var found = d.rows.filter(function (r) { return r.paper !== "00" && (r.no + ":" + r.label + " " + (r.key || "") + " " + r.tag + " " + r.paper + " " + r.text).toLowerCase().indexOf(query) >= 0; });
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
  q.addEventListener("input", function () { query = q.value.trim().toLowerCase(); render(); corpusSearch(); });
  build(); render();
  if (location.hash) { var t = document.getElementById(location.hash.slice(1)); if (t) (t.closest("tr") || t).classList.add("target"); }   /* the label anchor is the row, the key anchor a cell of it */
  if (window.REGISTER_URL && /^#p\d{5}$/.test(location.hash) && !document.getElementById(location.hash.slice(1))) {   /* a key of another ledger: the register says whose, and the predicate opens on its page */
    loadReg(function (d) { var k = location.hash.slice(1), hit = d.rows.filter(function (r) { return r.key === k; })[0]; if (hit) location.replace(hit.page); });
  }
}
if (typeof LEDGER_PREVIEW === "undefined") initLedger(document);
