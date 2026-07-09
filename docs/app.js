const graphData = window.DICT_DEPENDENCY_DATA;
const nodeById = new Map(graphData.nodes.map((node) => [node.id, node]));

const section5DefinitionRoots = Array.from({ length: 23 }, (_, index) =>
  `S05_D${String(index + 1).padStart(2, "0")}`
);
const section5LemmaRoots = Array.from({ length: 26 }, (_, index) =>
  `S05_L${String(index + 1).padStart(2, "0")}`
);
const section5Roots = [...section5DefinitionRoots, ...section5LemmaRoots];

function collectTransitiveDeps(rootIds) {
  const open = new Set();
  const visiting = new Set();

  function visit(id) {
    if (visiting.has(id)) return;
    const node = nodeById.get(id);
    if (!node) return;
    visiting.add(id);

    const deps = node.deps || [];
    if (deps.length > 0) open.add(id);
    deps.forEach(visit);

    visiting.delete(id);
  }

  rootIds.forEach(visit);
  return Array.from(open);
}

const rootViews = {
  paper: {
    label: "Paper map",
    roots: [
      "Thm1_1", "Thm2_1", "Thm2_2", "L2_3", "Def2_4",
      "S03_01", "S03_02", "L4_1", "S04_04", "S04_05", "S04_06",
      "S04_07", "S04_08", "S04_09", "Thm4_10",
      "S05_L18", "S05_L19", "S05_L20", "S05_L10", "S05_L01", "S05_D01",
    ],
    open: ["Thm1_1", "Thm4_10", "S05_L19", "S05_L20", "S05_L18"],
  },
  main: {
    label: "Main theorem",
    roots: ["Thm1_1"],
    open: ["Thm1_1", "L4_13", "Prop4_12", "Thm4_10", "S05_L19", "S05_L20", "S05_L17", "S05_L18"],
  },
  spectral: {
    label: "Spectral bridge",
    roots: ["Thm4_10"],
    open: collectTransitiveDeps(["Thm4_10"]),
  },
  definitions: {
    label: "Definitions",
    roots: section5DefinitionRoots,
    open: ["S05_D01", "S05_D02", "S05_D03", "S05_D04", "S05_D05"],
  },
  section5: {
    label: "Section 5",
    roots: section5Roots,
    open: ["S05_L19", "S05_L20", "S05_L18", "S05_L17", "S05_L10", "S05_L01"],
  },
  certificates: {
    label: "Finite certificates",
    roots: ["S05_L24", "S05_L26", "S05_L22", "S05_L21"],
    open: ["S05_L24", "S05_L26", "S05_L22", "S05_L21"],
  },
  appendix: {
    label: "Appendix A boundary",
    roots: ["AppA_01", "AppA_02", "AppA_03", "AppA_04"],
    open: ["AppA_01", "AppA_02", "AppA_03", "AppA_04"],
  },
};

const state = {
  view: "main",
  query: "",
  status: "all",
  selectedId: "Thm1_1",
  expanded: new Set(rootViews.main.open),
};

function sourceUrl(file) {
  return `${graphData.repoUrl}/blob/main/${file}`;
}

function statusLabel(status) {
  const labels = {
    proven: "Proven",
    external: "External",
    interface: "Interface",
  };
  return labels[status] || status;
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function termRefs(node) {
  return (node.terms || [])
    .filter((term) => term?.text && nodeById.has(term.target))
    .slice(0, 10);
}

function renderStatementMarkup(node) {
  let html = escapeHtml(node.statement || node.summary || "");
  const terms = termRefs(node).sort((a, b) => b.text.length - a.text.length);
  const used = new Set();
  terms.forEach((term, index) => {
    const escaped = escapeHtml(term.text);
    if (!escaped || used.has(term.text.toLowerCase())) return;
    const pattern = new RegExp(`\\b${escaped.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "i");
    if (!pattern.test(html)) return;
    used.add(term.text.toLowerCase());
    html = html.replace(
      pattern,
      `<button type="button" class="term-link" data-term-target="${term.target}" data-term-index="${index}">${escaped}</button>`
    );
  });
  return html;
}

function renderTermChips(node) {
  const terms = termRefs(node);
  if (!terms.length) return "";
  return `
    <div class="term-list" aria-label="Referenced definitions">
      ${terms
        .map((term) => `<button type="button" class="term-chip" data-term-target="${term.target}">${escapeHtml(term.text)}</button>`)
        .join("")}
    </div>
  `;
}

function attachTermHandlers(root) {
  root.querySelectorAll("[data-term-target]").forEach((button) => {
    button.addEventListener("click", (event) => {
      event.stopPropagation();
      openOverlay(button.dataset.termTarget);
    });
  });
}

function nodeWeight(node) {
  return { hero: 0, major: 1, normal: 2, minor: 3 }[node.importance] ?? 4;
}

function getDeps(node) {
  return (node.deps || [])
    .map((id) => nodeById.get(id))
    .filter(Boolean)
    .sort((a, b) => nodeWeight(a) - nodeWeight(b) || a.label.localeCompare(b.label));
}

function nodeMatches(node) {
  if (state.status !== "all" && node.status !== state.status) return false;
  if (!state.query) return true;
  const haystack = [
    node.id,
    node.label,
    node.title,
    node.file,
    node.section,
    node.status,
    node.summary,
    ...(node.wrappers || []),
  ].join(" ").toLowerCase();
  return haystack.includes(state.query.toLowerCase());
}

function subtreeHasMatch(node, seen = new Set()) {
  if (seen.has(node.id)) return false;
  seen.add(node.id);
  if (nodeMatches(node)) return true;
  return getDeps(node).some((dep) => subtreeHasMatch(dep, seen));
}

function shouldRenderNode(node) {
  if (!state.query && state.status === "all") return true;
  return subtreeHasMatch(node);
}

function dependentsOf(id) {
  return graphData.nodes
    .filter((node) => node.deps?.includes(id))
    .sort((a, b) => nodeWeight(a) - nodeWeight(b) || a.label.localeCompare(b.label));
}

function nodeClasses(node, path, repeated) {
  return [
    "dag-node",
    `importance-${node.importance || "normal"}`,
    `status-${node.status}`,
    `kind-${node.kind}`,
    state.selectedId === node.id ? "selected" : "",
    state.expanded.has(node.id) ? "expanded" : "",
    repeated ? "repeated" : "",
    path.length === 0 ? "root-node" : "",
  ].join(" ");
}

function renderNode(node, path = []) {
  const repeated = path.includes(node.id);
  if (!shouldRenderNode(node)) return null;

  const deps = getDeps(node).filter(shouldRenderNode);
  const isExpanded = state.expanded.has(node.id) && deps.length > 0 && !repeated;
  const item = document.createElement("li");
  item.className = "dag-item";
  item.dataset.id = node.id;

  const button = document.createElement("button");
  button.type = "button";
  button.className = nodeClasses(node, path, repeated);
  button.setAttribute("aria-expanded", String(isExpanded));
  button.innerHTML = `
    <span class="node-label">${node.label}</span>
    <span class="node-title">${node.title}</span>
  `;
  button.addEventListener("click", () => {
    state.selectedId = node.id;
    if (!repeated && deps.length > 0) {
      if (state.expanded.has(node.id)) {
        state.expanded.delete(node.id);
      } else {
        state.expanded.add(node.id);
      }
    }
    render();
  });
  item.appendChild(button);

  if (state.selectedId === node.id) {
    item.appendChild(renderInlineDetails(node, deps.length));
  }

  if (isExpanded) {
    const children = document.createElement("ol");
    children.className = "dag-children";
    deps.forEach((dep) => {
      const child = renderNode(dep, [...path, node.id]);
      if (child) children.appendChild(child);
    });
    item.appendChild(children);
  }

  return item;
}

function renderInlineDetails(node, depCount) {
  const details = document.createElement("div");
  details.className = "inline-details";
  const wrappers = node.wrappers?.length
    ? node.wrappers.map((wrapper) => `<code>${wrapper}</code>`).join(" ")
    : "<span class=\"muted\">No wrapper listed.</span>";
  const usedBy = dependentsOf(node.id)
    .map((dep) => `<button type="button" class="tiny-link" data-jump="${dep.id}">${dep.label}</button>`)
    .join("");
  details.innerHTML = `
    <p class="statement">${renderStatementMarkup(node)}</p>
    ${renderTermChips(node)}
    <dl>
      <dt>Lean file</dt>
      <dd><a href="${sourceUrl(node.file)}" target="_blank" rel="noreferrer">${node.file}</a></dd>
      <dt>Wrappers</dt>
      <dd>${wrappers}</dd>
    </dl>
    <div class="node-foot">
      <span>${depCount} dependencies</span>
      <span>${usedBy ? "Used by " + usedBy : "No dependents listed in this graph"}</span>
    </div>
  `;
  attachTermHandlers(details);
  details.querySelectorAll("[data-jump]").forEach((button) => {
    button.addEventListener("click", (event) => {
      event.stopPropagation();
      state.selectedId = button.dataset.jump;
      state.expanded.add(button.dataset.jump);
      render();
    });
  });
  return details;
}

function openOverlay(id) {
  const node = nodeById.get(id);
  const root = document.querySelector("#overlay-root");
  if (!node || !root) return;

  root.innerHTML = `
    <div class="overlay-backdrop" role="presentation"></div>
    <section class="term-overlay" role="dialog" aria-modal="true" aria-label="${escapeHtml(node.label)} ${escapeHtml(node.title)}">
      <button type="button" class="overlay-close" aria-label="Close definition overlay">x</button>
      <div class="overlay-kicker">${escapeHtml(statusLabel(node.status))}</div>
      <h2>${escapeHtml(node.label)} <span>${escapeHtml(node.title)}</span></h2>
      <p class="statement">${renderStatementMarkup(node)}</p>
      ${renderTermChips(node)}
      <dl>
        <dt>Lean file</dt>
        <dd><a href="${sourceUrl(node.file)}" target="_blank" rel="noreferrer">${escapeHtml(node.file)}</a></dd>
        <dt>Wrappers</dt>
        <dd>${node.wrappers?.length ? node.wrappers.map((wrapper) => `<code>${escapeHtml(wrapper)}</code>`).join(" ") : "No wrapper listed."}</dd>
      </dl>
    </section>
  `;
  root.classList.add("active");
  attachTermHandlers(root);

  const close = () => {
    root.classList.remove("active");
    root.textContent = "";
  };
  root.querySelector(".overlay-backdrop").addEventListener("click", close);
  root.querySelector(".overlay-close").addEventListener("click", close);
  root.querySelector(".overlay-close").focus();
}

function renderTree() {
  const tree = document.querySelector("#dag");
  tree.textContent = "";
  const rootList = document.createElement("ol");
  rootList.className = "dag-root-list";
  rootViews[state.view].roots
    .map((id) => nodeById.get(id))
    .filter(Boolean)
    .forEach((root) => {
      const rootNode = renderNode(root, []);
      if (rootNode) rootList.appendChild(rootNode);
    });

  if (!rootList.children.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "No nodes match the current filters.";
    tree.appendChild(empty);
  } else {
    tree.appendChild(rootList);
  }
}

function renderTabs() {
  const tabs = document.querySelector("#tabs");
  tabs.textContent = "";
  Object.entries(rootViews).forEach(([key, view]) => {
    const tab = document.createElement("button");
    tab.type = "button";
    tab.className = key === state.view ? "tab active" : "tab";
    tab.textContent = view.label;
    tab.addEventListener("click", () => {
      state.view = key;
      state.expanded = new Set(view.open);
      state.selectedId = view.roots[0];
      render();
    });
    tabs.appendChild(tab);
  });
}

function renderStats() {
  const stats = document.querySelector("#stats");
  const counts = graphData.nodes.reduce((acc, node) => {
    acc[node.status] = (acc[node.status] || 0) + 1;
    acc.total += 1;
    return acc;
  }, { total: 0 });
  stats.innerHTML = `
    <span><strong>${counts.total}</strong> nodes</span>
    <span><strong>${counts.proven || 0}</strong> proven</span>
    <span><strong>${counts.external || 0}</strong> external</span>
    <span><strong>${counts.interface || 0}</strong> interfaces</span>
  `;
}

function expandVisible() {
  const visible = new Set();
  function walk(node, seen = new Set()) {
    if (!node || seen.has(node.id) || !shouldRenderNode(node)) return;
    seen.add(node.id);
    visible.add(node.id);
    getDeps(node).forEach((dep) => walk(dep, seen));
  }
  rootViews[state.view].roots.forEach((id) => walk(nodeById.get(id)));
  state.expanded = visible;
  render();
}

function collapseVisible() {
  state.expanded = new Set();
  render();
}

function render() {
  renderTabs();
  renderStats();
  renderTree();
}

document.querySelector("#search").addEventListener("input", (event) => {
  state.query = event.target.value;
  render();
});

document.querySelector("#status-filter").addEventListener("change", (event) => {
  state.status = event.target.value;
  render();
});

document.querySelector("#expand-all").addEventListener("click", expandVisible);
document.querySelector("#collapse-all").addEventListener("click", collapseVisible);

render();
