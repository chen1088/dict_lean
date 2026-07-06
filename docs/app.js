const graphData = window.DICT_DEPENDENCY_DATA;
const nodeById = new Map(graphData.nodes.map((node) => [node.id, node]));

const state = {
  query: "",
  status: "all",
  view: "main",
  selectedId: "Thm1_1",
  focusMode: false,
};

const views = {
  main: {
    label: "Main Spine",
    sections: ["Main spine", "Spectral bridge", "Finite certificates", "External inputs"],
    seed: ["Thm1_1", "L4_13", "Prop4_12", "Thm4_10", "S05_27", "S05_28"],
  },
  section5: {
    label: "Section 5",
    sections: [
      "Section 5 tableau layer",
      "Tableau branching",
      "Matching algebra",
      "Spectral bridge",
      "Finite certificates",
      "Definitions",
      "Appendix A",
      "External inputs",
    ],
  },
  certificates: {
    label: "Finite Certificates",
    sections: ["Finite certificates", "Tableau branching", "Definitions"],
    seed: ["S05_30", "S05_32", "S05_34"],
  },
  aux: {
    label: "Aux Helpers",
    sections: ["Section 5 tableau layer", "Tableau branching", "Finite certificates", "Spectral bridge", "Section 4", "Definitions"],
    auxOnly: true,
  },
  all: {
    label: "All Nodes",
    sections: null,
  },
};

function sourceUrl(file) {
  return `${graphData.repoUrl}/blob/main/${file}`;
}

function statusLabel(status) {
  const labels = {
    proved: "Proved",
    "proved-from-external": "Proved + External Input",
    external: "External",
    interface: "Definition / Interface",
  };
  return labels[status] || status;
}

function relationSets(selected) {
  const deps = new Set(selected?.deps || []);
  const dependents = new Set(
    graphData.nodes
      .filter((node) => node.deps?.includes(selected?.id))
      .map((node) => node.id)
  );
  return { deps, dependents };
}

function shouldShowByView(node) {
  const view = views[state.view];
  if (view.auxOnly && node.kind !== "aux") return false;
  if (view.sections && !view.sections.includes(node.section)) return false;
  if (view.seed && !view.seed.includes(node.id)) {
    const seedSet = new Set(view.seed);
    const supportsSeed = graphData.nodes.some((candidate) =>
      seedSet.has(candidate.id) && candidate.deps?.includes(node.id)
    );
    const usesSeed = node.deps?.some((dep) => seedSet.has(dep));
    return supportsSeed || usesSeed || node.importance === "hero";
  }
  return true;
}

function matchesFilters(node) {
  if (state.status !== "all" && node.status !== state.status) return false;
  if (state.query) {
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
    if (!haystack.includes(state.query.toLowerCase())) return false;
  }
  if (state.focusMode && state.selectedId) {
    const selected = nodeById.get(state.selectedId);
    const { deps, dependents } = relationSets(selected);
    return node.id === selected.id || deps.has(node.id) || dependents.has(node.id);
  }
  return shouldShowByView(node);
}

function nodeClass(node) {
  return [
    "node-button",
    `importance-${node.importance || "normal"}`,
    `status-${node.status}`,
    `kind-${node.kind}`,
    node.id === state.selectedId ? "selected" : "",
  ].join(" ");
}

function renderNodeButton(node) {
  const button = document.createElement("button");
  button.className = nodeClass(node);
  button.type = "button";
  button.dataset.id = node.id;
  button.innerHTML = `
    <span class="node-label">${node.label}</span>
    <span class="node-title">${node.title}</span>
    <span class="node-meta">${statusLabel(node.status)}</span>
  `;
  button.addEventListener("click", () => {
    state.selectedId = node.id;
    render();
  });
  return button;
}

function renderGraph() {
  const graph = document.querySelector("#graph");
  graph.textContent = "";

  const nodes = graphData.nodes.filter(matchesFilters);
  const sections = [...new Set(nodes.map((node) => node.section))];

  if (!nodes.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "No nodes match the current filters.";
    graph.appendChild(empty);
    return;
  }

  sections.forEach((section) => {
    const group = document.createElement("section");
    group.className = "graph-section";
    const groupNodes = nodes.filter((node) => node.section === section);
    group.innerHTML = `
      <div class="section-heading">
        <h2>${section}</h2>
        <span>${groupNodes.length} nodes</span>
      </div>
      <div class="node-grid"></div>
    `;
    const grid = group.querySelector(".node-grid");
    groupNodes
      .sort((a, b) => {
        const weights = { hero: 0, major: 1, normal: 2, minor: 3 };
        return (weights[a.importance] ?? 4) - (weights[b.importance] ?? 4) || a.label.localeCompare(b.label);
      })
      .forEach((node) => grid.appendChild(renderNodeButton(node)));
    graph.appendChild(group);
  });
}

function renderRelationList(title, ids, className) {
  const items = ids
    .map((id) => nodeById.get(id))
    .filter(Boolean)
    .map((node) => `
      <button class="relation-pill ${className}" data-id="${node.id}">
        <strong>${node.label}</strong>
        <span>${node.title}</span>
      </button>
    `)
    .join("");
  return `
    <div class="relation-block">
      <h3>${title}</h3>
      <div class="relation-list">${items || "<span class=\"muted\">None recorded.</span>"}</div>
    </div>
  `;
}

function renderDetails() {
  const selected = nodeById.get(state.selectedId) || graphData.nodes[0];
  state.selectedId = selected.id;
  const { deps, dependents } = relationSets(selected);
  const panel = document.querySelector("#details");
  panel.innerHTML = `
    <div class="detail-card status-${selected.status}">
      <div class="detail-kicker">${selected.section} / ${selected.kind}</div>
      <h2>${selected.label}: ${selected.title}</h2>
      <p>${selected.summary}</p>
      <div class="detail-badges">
        <span>${statusLabel(selected.status)}</span>
        <span>${selected.importance || "normal"}</span>
      </div>
      <dl>
        <dt>Lean file</dt>
        <dd><a href="${sourceUrl(selected.file)}" target="_blank" rel="noreferrer">${selected.file}</a></dd>
        <dt>Main wrappers</dt>
        <dd>${selected.wrappers?.length ? selected.wrappers.map((w) => `<code>${w}</code>`).join(" ") : "<span class=\"muted\">None listed.</span>"}</dd>
      </dl>
      ${renderRelationList("Depends on", [...deps], "dep")}
      ${renderRelationList("Used by", [...dependents], "dependent")}
    </div>
  `;

  panel.querySelectorAll(".relation-pill").forEach((button) => {
    button.addEventListener("click", () => {
      state.selectedId = button.dataset.id;
      render();
    });
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

function renderTabs() {
  const tabs = document.querySelector("#tabs");
  tabs.textContent = "";
  Object.entries(views).forEach(([key, view]) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = key === state.view ? "tab active" : "tab";
    button.textContent = view.label;
    button.addEventListener("click", () => {
      state.view = key;
      state.focusMode = false;
      document.querySelector("#focus-toggle").classList.remove("active");
      render();
    });
    tabs.appendChild(button);
  });
}

function render() {
  renderTabs();
  renderStats();
  renderGraph();
  renderDetails();
}

document.querySelector("#search").addEventListener("input", (event) => {
  state.query = event.target.value;
  render();
});

document.querySelector("#status-filter").addEventListener("change", (event) => {
  state.status = event.target.value;
  render();
});

document.querySelector("#focus-toggle").addEventListener("click", () => {
  state.focusMode = !state.focusMode;
  document.querySelector("#focus-toggle").classList.toggle("active", state.focusMode);
  render();
});

render();
