/* register.js — the register view: papers × blocks × tags over the records of register.json, the rows' cells from the pages; both in register-data.js (a script: the page opens from a local file too). No framework. */
(function () {
  "use strict";
  var BLOCKS = {P: "Predictions", T: "Tasks", X: "Explains", Y: "Hypotheses", Z: "Horizon"};
  var TAGS = {G: "ground", P: "pillar", T: "theorem", D: "definition", R: "realisation", I: "import", "Ω": "Ω-hard", O: "open"};
  var st = {paper: "all", block: "T", tag: "all", q: ""};
  var qs = new URLSearchParams(location.search);
  ["paper", "block", "tag", "q"].forEach(function (k) { if (qs.has(k)) st[k] = qs.get(k); });
  if (st.paper === "all" && st.block === "all") st.block = "T";          /* the rule: all papers with all blocks is no view */
  var reg = null, frags = null, papers = {}, order = [], allTags = {};
  var tbody = document.getElementById("rows"), count = document.getElementById("count"), empty = document.getElementById("empty"), q = document.getElementById("q");
  q.value = st.q;
  function tagsOf(r) { return r.tag.split("|"); }
  function text(r) { return (r.no + ":" + r.label + " " + (r.key || "") + " " + r.tag + " " + r.paper + " " + r.text).toLowerCase(); }
  function match(r, skip) {
    if (skip !== "paper" && st.paper !== "all" && r.paper !== st.paper) return false;
    if (skip !== "block" && st.block !== "all" && r.block !== st.block) return false;
    if (skip !== "tag" && st.tag !== "all" && tagsOf(r).indexOf(st.tag) < 0) return false;
    if (st.q && text(r).indexOf(st.q) < 0) return false;
    return true;
  }
  function pill(box, key, label, dot, n, active, onclick) {
    var b = document.createElement("button"); b.type = "button"; b.setAttribute("aria-pressed", String(active));
    b.innerHTML = (dot ? '<span class="dot ' + dot + '"></span>' : "") + label + ' <span class="n">' + n + "</span>";
    b.addEventListener("click", onclick); box.appendChild(b);
  }
  function build() {
    var pb = document.getElementById("papers"), bb = document.getElementById("blocks"), tb = document.getElementById("tags");
    pb.innerHTML = '<span class="cap">Papers</span>'; bb.innerHTML = '<span class="cap">Blocks</span>'; tb.innerHTML = '<span class="cap">Status</span>';
    var cp = {all: 0}, cb = {all: 0}, ct = {all: 0};
    reg.rows.forEach(function (r) {
      if (match(r, "paper")) { if (st.block !== "all" || r.block === "T") cp.all++; cp[r.paper] = (cp[r.paper] || 0) + 1; }   /* the All counts say what the click yields under the rule */
      if (match(r, "block")) { if (st.paper !== "all" || r.paper === "00") cb.all++; if (BLOCKS[r.block]) cb[r.block] = (cb[r.block] || 0) + 1; }
      if (match(r, "tag")) { ct.all++; tagsOf(r).forEach(function (t) { ct[t] = (ct[t] || 0) + 1; }); }
    });
    pill(pb, "all", "All", "", cp.all, st.paper === "all", function () { st.paper = "all"; if (st.block === "all") st.block = "T"; update(); });
    order.forEach(function (k) { pill(pb, k, k === "00" ? "00 master" : k, "", cp[k] || 0, st.paper === k, function () { st.paper = (st.paper === k) ? "all" : k; if (st.paper === "all" && st.block === "all") st.block = "T"; update(); }); });
    pill(bb, "all", "All", "", cb.all, st.block === "all", function () { st.block = "all"; if (st.paper === "all") st.paper = "00"; update(); });
    Object.keys(BLOCKS).forEach(function (k) { pill(bb, k, k + " · " + BLOCKS[k], "", cb[k] || 0, st.block === k, function () { st.block = (st.block === k) ? "all" : k; if (st.block === "all" && st.paper === "all") st.paper = "00"; update(); }); });
    pill(tb, "all", "All", "", ct.all, st.tag === "all", function () { st.tag = "all"; update(); });
    Object.keys(TAGS).forEach(function (k) { if (allTags[k]) pill(tb, k, TAGS[k], "dot t-" + (k === "Ω" ? "om" : k.toLowerCase()), ct[k] || 0, st.tag === k, function () { st.tag = (st.tag === k) ? "all" : k; update(); }); });
  }
  function badge(tag) { return tag.split("|").map(function (t) { return '<span class="tag ' + (t === "Ω" ? "om" : t.toLowerCase()) + '" title="' + (TAGS[t] || t) + '">' + t + "</span>"; }).join(" "); }
  var pending = [], observer = null;
  function typeset(nodes) { if (window.MathJax && MathJax.typesetPromise) MathJax.startup.promise.then(function () { return MathJax.typesetPromise(nodes); }); }
  function render() {
    var rows = reg.rows.filter(function (r) { return match(r); });
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
      var f = frags.rows[r.key] || {statement: "", source: ""};
      html.push('<tr data-key="' + (r.key || "") + '"><td class="lab"><a href="' + r.page + '" title="the predicate in its ledger">' + (r.paper === "00" ? "00" : r.no) + ":" + r.label + '</a><span class="key" id="' + (r.key || "") + '">' + (r.key || "") + "</span></td>"
              + '<td class="pred">' + f.statement + '</td><td class="status">' + badge(r.tag) + '</td><td class="src">' + f.source + "</td></tr>");
    });
    tbody.innerHTML = html.join("");
    count.textContent = rows.length + " of " + reg.rows.length; empty.hidden = rows.length > 0;
    /* typeset the first rows now, the rest as they scroll into view (60 at a time) */
    var trs = Array.prototype.slice.call(tbody.querySelectorAll("tr[data-key]"));
    trs.forEach(function (t) { t.dataset.ts = "0"; });
    function chunk(from) { var list = []; for (var i = from; i < trs.length && list.length < 60; i++) if (trs[i].dataset.ts === "0") { trs[i].dataset.ts = "1"; list.push(trs[i]); } if (list.length) typeset(list); }
    chunk(0);
    if ("IntersectionObserver" in window && trs.length > 60) {
      observer = new IntersectionObserver(function (es) { es.forEach(function (e) { if (e.isIntersecting && e.target.dataset.ts === "0") chunk(trs.indexOf(e.target)); }); }, {rootMargin: "600px 0px"});
      trs.forEach(function (t) { observer.observe(t); });
    }
    var k = location.hash.slice(1), row = k && document.getElementById(k);
    if (row) { row.closest("tr").classList.add("target"); row.closest("tr").scrollIntoView({block: "center"}); }
  }
  function update() {
    var u = new URLSearchParams(); if (st.paper !== "all") u.set("paper", st.paper); if (st.block !== "all") u.set("block", st.block); if (st.tag !== "all") u.set("tag", st.tag); if (st.q) u.set("q", st.q);
    history.replaceState(null, "", location.pathname + (u.toString() ? "?" + u.toString() : "") + location.hash);
    build(); render();
  }
  q.addEventListener("input", function () { st.q = q.value.trim().toLowerCase(); update(); });
  function withData(then) {
    if (window.FRC_REGISTER) { then(); return; }
    var sc = document.createElement("script"); sc.src = "register-data.js"; sc.onload = then; document.head.appendChild(sc);
  }
  withData(function () {
    reg = window.FRC_REGISTER; frags = window.FRC_REGISTER_ROWS;
    reg.header.papers.forEach(function (p) { papers[p.key] = p; order.push(p.key); });
    reg.rows.forEach(function (r) { tagsOf(r).forEach(function (t) { allTags[t] = true; }); });
    var k = location.hash.slice(1);
    if (/^p\d{5}$/.test(k)) { var hit = reg.rows.filter(function (r) { return r.key === k; })[0]; if (hit) { st.paper = hit.paper; st.block = "all"; } }   /* a key: its paper, every block */
    update();
  });
})();
