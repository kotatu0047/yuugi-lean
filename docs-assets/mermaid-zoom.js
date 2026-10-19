// mermaid の図を描き、図ごとに「全画面で見る」ボタンを付ける。
// 全画面では、ホイール・＋−ボタンで拡大縮小、ドラッグで移動、「全体を表示」で画面に合わせる。Esc か「閉じる」で戻る。
// URL の末尾を #fullscreen-1 にすると、そのページの1番目の図を全画面で開く。
(function () {
  const MERMAID = "https://cdn.jsdelivr.net/npm/mermaid@10.9.1/dist/mermaid.esm.min.mjs";
  const dark = () => document.body.getAttribute("data-md-color-scheme") === "slate";
  const diagrams = [];
  let mermaidLib = null;
  let serial = 0;

  // 図を描く（色はライト・ダークに合わせる）
  async function draw(view, code) {
    mermaidLib.initialize({ startOnLoad: false, theme: dark() ? "dark" : "default", securityLevel: "strict" });
    try {
      const { svg } = await mermaidLib.render("cg-mermaid-" + serial++, code);
      view.innerHTML = svg;
      return true;
    } catch (e) {
      view.textContent = "図を描けませんでした：" + e;
      return false;
    }
  }

  async function renderAll() {
    const blocks = Array.from(document.querySelectorAll("pre.cg-mermaid"));
    if (blocks.length === 0) return;
    mermaidLib = (await import(MERMAID)).default;
    for (const pre of blocks) {
      const code = pre.textContent;
      const box = document.createElement("div");
      box.className = "cg-diagram";
      const bar = document.createElement("div");
      bar.className = "cg-diagram-bar";
      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = "md-button cg-full-button";
      btn.textContent = "全画面で見る";
      bar.appendChild(btn);
      const view = document.createElement("div");
      view.className = "cg-diagram-view";
      view.title = "クリックで全画面";
      box.append(bar, view);
      pre.replaceWith(box);
      view.dataset.code = code;
      if (!(await draw(view, code))) continue;
      const index = diagrams.length;
      diagrams.push(view);
      btn.addEventListener("click", () => open(index));
      view.addEventListener("click", () => open(index));
    }
    // ライト・ダークを切り替えたら描き直す
    let scheme = dark();
    new MutationObserver(async () => {
      if (dark() === scheme) return;
      scheme = dark();
      for (const v of diagrams) await draw(v, v.dataset.code);
    }).observe(document.body, { attributes: true, attributeFilter: ["data-md-color-scheme"] });
    const m = location.hash.match(/^#fullscreen-(\d+)$/);
    if (m && diagrams[Number(m[1]) - 1]) open(Number(m[1]) - 1);
  }

  function open(index) {
    const src = diagrams[index].querySelector("svg");
    if (!src) return;
    const overlay = document.createElement("div");
    overlay.className = "cg-overlay";
    const tools = document.createElement("div");
    tools.className = "cg-overlay-tools";
    const stage = document.createElement("div");
    stage.className = "cg-overlay-stage";
    const layer = document.createElement("div");
    layer.className = "cg-overlay-layer";
    const svg = src.cloneNode(true);
    // 元の大きさで描き、拡大縮小は transform で行う
    const vb = svg.viewBox && svg.viewBox.baseVal;
    const w = vb && vb.width ? vb.width : src.getBoundingClientRect().width;
    const h = vb && vb.height ? vb.height : src.getBoundingClientRect().height;
    svg.removeAttribute("style");
    svg.setAttribute("width", w);
    svg.setAttribute("height", h);
    layer.appendChild(svg);
    stage.appendChild(layer);

    let scale = 1, x = 0, y = 0;
    const apply = () => { layer.style.transform = `translate(${x}px, ${y}px) scale(${scale})`; label.textContent = Math.round(scale * 100) + "%"; };
    const fit = () => {
      const r = stage.getBoundingClientRect();
      scale = Math.min(r.width / w, r.height / h) * 0.95;
      x = (r.width - w * scale) / 2;
      y = (r.height - h * scale) / 2;
      apply();
    };
    // 画面の点 (cx, cy) を中心に拡大縮小する
    const zoomAt = (factor, cx, cy) => {
      const next = Math.min(20, Math.max(0.05, scale * factor));
      const k = next / scale;
      x = cx - (cx - x) * k;
      y = cy - (cy - y) * k;
      scale = next;
      apply();
    };
    const center = () => { const r = stage.getBoundingClientRect(); return [r.width / 2, r.height / 2]; };

    const button = (text, onClick, title) => {
      const b = document.createElement("button");
      b.type = "button";
      b.className = "md-button";
      b.textContent = text;
      if (title) b.title = title;
      b.addEventListener("click", onClick);
      tools.appendChild(b);
      return b;
    };
    button("＋", () => zoomAt(1.25, ...center()), "拡大");
    button("−", () => zoomAt(0.8, ...center()), "縮小");
    button("全体を表示", fit);
    button("等倍", () => { const [cx, cy] = center(); zoomAt(1 / scale, cx, cy); });
    const label = document.createElement("span");
    label.className = "cg-overlay-scale";
    tools.appendChild(label);
    const hint = document.createElement("span");
    hint.className = "cg-overlay-hint";
    hint.textContent = "ホイールで拡大縮小・ドラッグで移動・Esc で閉じる";
    tools.appendChild(hint);
    const close = () => {
      overlay.remove();
      document.removeEventListener("keydown", onKey);
      document.documentElement.style.overflow = "";
      if (location.hash.startsWith("#fullscreen-")) history.replaceState(null, "", location.pathname + location.search);
    };
    button("閉じる", close).classList.add("cg-close");
    const onKey = (e) => {
      if (e.key === "Escape") close();
      else if (e.key === "+" || e.key === "=") zoomAt(1.25, ...center());
      else if (e.key === "-") zoomAt(0.8, ...center());
      else if (e.key === "0") fit();
    };
    document.addEventListener("keydown", onKey);

    stage.addEventListener("wheel", (e) => {
      e.preventDefault();
      const r = stage.getBoundingClientRect();
      zoomAt(Math.exp(-e.deltaY * 0.0015), e.clientX - r.left, e.clientY - r.top);
    }, { passive: false });
    // ドラッグで移動（2本指ではピンチで拡大縮小）
    const pointers = new Map();
    let last = null, pinch = null;
    stage.addEventListener("pointerdown", (e) => {
      stage.setPointerCapture(e.pointerId);
      pointers.set(e.pointerId, [e.clientX, e.clientY]);
      last = [e.clientX, e.clientY];
      stage.classList.add("cg-dragging");
    });
    stage.addEventListener("pointermove", (e) => {
      if (!pointers.has(e.pointerId)) return;
      pointers.set(e.pointerId, [e.clientX, e.clientY]);
      if (pointers.size === 2) {
        const [a, b] = Array.from(pointers.values());
        const d = Math.hypot(a[0] - b[0], a[1] - b[1]);
        const r = stage.getBoundingClientRect();
        if (pinch) zoomAt(d / pinch, (a[0] + b[0]) / 2 - r.left, (a[1] + b[1]) / 2 - r.top);
        pinch = d;
        return;
      }
      x += e.clientX - last[0];
      y += e.clientY - last[1];
      last = [e.clientX, e.clientY];
      apply();
    });
    const up = (e) => {
      pointers.delete(e.pointerId);
      pinch = null;
      if (pointers.size === 1) last = Array.from(pointers.values())[0];
      if (pointers.size === 0) stage.classList.remove("cg-dragging");
    };
    stage.addEventListener("pointerup", up);
    stage.addEventListener("pointercancel", up);
    stage.addEventListener("dblclick", fit);

    overlay.append(tools, stage);
    document.body.appendChild(overlay);
    document.documentElement.style.overflow = "hidden";
    if (!location.hash.startsWith("#fullscreen-")) history.replaceState(null, "", "#fullscreen-" + (index + 1));
    fit();
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", renderAll);
  else renderAll();
})();
