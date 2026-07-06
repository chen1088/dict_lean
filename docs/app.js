const graphData = window.DICT_DEPENDENCY_DATA;
const nodeById = new Map(graphData.nodes.map((node) => [node.id, node]));

const section5Roots = [
  "S05_01", "S05_02", "S05_03", "S05_04", "S05_05",
  "S05_06", "S05_07", "S05_08", "S05_09", "S05_10", "S05_11",
  "S05_12", "S05_13", "S05_14", "S05_15", "S05_16", "S05_17",
  "S05_18", "S05_19", "S05_20", "S05_21", "S05_22", "S05_23",
  "S05_24", "S05_25", "S05_26", "S05_27", "S05_28", "S05_29",
  "S05_30", "S05_31", "S05_32", "S05_33", "S05_34", "S05_35",
  "S05_36", "S05_37", "S05_38", "S05_39",
];

const rootViews = {
  paper: {
    label: "Paper map",
    roots: [
      "Thm1_1", "Thm2_1", "Thm2_2", "L2_3", "Def2_4",
      "S03_01", "S03_02", "L4_1", "S04_04", "S04_05", "S04_06",
      "S04_07", "S04_08", "S04_09", "Thm4_10",
      "S05_32", "S05_33", "S05_23", "S05_06", "S05_01",
    ],
    open: ["Thm1_1", "Thm4_10", "S05_32", "S05_33"],
  },
  main: {
    label: "Main theorem",
    roots: ["Thm1_1"],
    open: ["Thm1_1", "L4_13", "Prop4_12", "Thm4_10", "S05_32", "S05_33"],
  },
  spectral: {
    label: "Spectral bridge",
    roots: ["Thm4_10"],
    open: ["Thm4_10", "S05_32", "S05_33", "S05_31"],
  },
  section5: {
    label: "Section 5",
    roots: section5Roots,
    open: ["S05_32", "S05_33", "S05_31", "S05_30", "S05_23", "S05_06"],
  },
  certificates: {
    label: "Finite certificates",
    roots: ["S05_37", "S05_39", "S05_35", "S05_21"],
    open: ["S05_37", "S05_39", "S05_35", "S05_21"],
  },
  appendix: {
    label: "Appendix A boundary",
    roots: ["AppA_EvenSpectralModel", "AppA_OddSpectralModel"],
    open: ["AppA_EvenSpectralModel", "AppA_OddSpectralModel"],
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
    proved: "Proved",
    "proved-from-external": "Proved + input",
    external: "External",
    interface: "Interface",
  };
  return labels[status] || status;
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
    <p>${node.summary}</p>
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
    <span><strong>${counts.proved || 0}</strong> proved</span>
    <span><strong>${counts["proved-from-external"] || 0}</strong> proved + input</span>
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
