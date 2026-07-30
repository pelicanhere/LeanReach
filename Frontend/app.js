const form = document.querySelector("#search-form");
const input = document.querySelector("#query");
const status = document.querySelector("#status");
const results = document.querySelector("#results");
const detail = document.querySelector("#detail");

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function sourceText(declaration) {
  const source = declaration.source;
  return `${source.file || source.moduleName}:${source.line}:${source.column}`;
}

function copyButton(text) {
  const button = element("button", "copy", "Copy");
  button.type = "button";
  button.addEventListener("click", async () => {
    await navigator.clipboard.writeText(text);
    button.textContent = "Copied";
    setTimeout(() => button.textContent = "Copy", 900);
  });
  return button;
}

function declarationCard(declaration, inspectable = true) {
  const card = element("article", "declaration");
  const heading = element("div", "declaration-heading");
  const name = element(inspectable ? "button" : "h2", "declaration-name", declaration.name);
  if (inspectable) {
    name.type = "button";
    name.addEventListener("click", () => inspect(declaration.queryName));
  }
  heading.append(name, copyButton(declaration.queryName));

  const signature = element("pre", "signature");
  signature.append(element("code", "", declaration.signature));
  const location = element("div", "location", sourceText(declaration));
  location.title = declaration.source.moduleName;
  card.append(heading, signature, location);
  return card;
}

function emptyState(message) {
  const node = element("div", "empty");
  node.append(element("strong", "", message));
  return node;
}

async function request(parameters) {
  status.textContent = "Loading…";
  const response = await fetch(`/json?${new URLSearchParams(parameters)}`);
  const data = await response.json();
  if (!response.ok || data.error) throw new Error(data.error || `HTTP ${response.status}`);
  status.textContent = "";
  return data;
}

async function search(query) {
  query = query.trim();
  if (!query) return;
  input.value = query;
  results.replaceChildren();
  detail.replaceChildren();
  history.replaceState({}, "", `?q=${encodeURIComponent(query)}`);
  try {
    const data = await request({q: query});
    const heading = element("div", "section-heading");
    heading.append(
      element("h1", "", "Matches"),
      element("span", "count", `${data.items.length} shown`),
    );
    results.append(heading);
    if (!data.items.length) {
      results.append(emptyState("No declaration name matched."));
      return;
    }
    const list = element("div", "result-list");
    data.items.forEach(item => list.append(declarationCard(item)));
    results.append(list);
  } catch (error) {
    status.textContent = "";
    results.append(emptyState(error.message));
  }
}

function relationColumn(label, items) {
  const column = element("section", "relation");
  const heading = element("div", "relation-heading");
  heading.append(element("h2", "", label), element("span", "count", String(items.length)));
  column.append(heading);
  if (!items.length) {
    column.append(emptyState("No direct dependencies."));
    return column;
  }
  items.forEach(item => column.append(declarationCard(item)));
  return column;
}

async function inspect(name) {
  detail.replaceChildren();
  detail.scrollIntoView({behavior: "smooth", block: "start"});
  history.replaceState({}, "", `?name=${encodeURIComponent(name)}`);
  try {
    const data = await request({name});
    const target = element("section", "target");
    target.append(element("div", "eyebrow", "Target"), declarationCard(data.target, false));
    const relations = element("div", "relations");
    relations.append(
      relationColumn("Upstream", data.upstream),
      relationColumn("Downstream", data.downstream),
    );
    detail.append(target, relations);
  } catch (error) {
    status.textContent = "";
    detail.append(emptyState(error.message));
  }
}

form.addEventListener("submit", event => {
  event.preventDefault();
  search(input.value);
});

document.querySelectorAll("[data-query]").forEach(button => {
  button.addEventListener("click", () => search(button.dataset.query));
});

const initial = new URLSearchParams(location.search);
if (initial.has("name")) inspect(initial.get("name"));
else if (initial.has("q")) search(initial.get("q"));
