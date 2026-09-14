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
  q.addEventListener("input", function () { query = q.value.trim().toLowerCase(); render(); });
  build(); render();
  if (location.hash) { var t = document.getElementById(location.hash.slice(1)); if (t) t.classList.add("target"); }
}
if (typeof LEDGER_PREVIEW === "undefined") initLedger(document);
