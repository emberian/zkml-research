"use strict";
(() => {
  const form = document.querySelector("#filters");
  const search = document.querySelector("#search");
  const topic = document.querySelector("#topic");
  const count = document.querySelector("#result-count");
  const empty = document.querySelector("#empty");
  const cards = [...document.querySelectorAll(".result-card")];
  const index = new Map(cards.map(card => [card, card.textContent.toLocaleLowerCase()]));
  let timer;

  function filter() {
    const terms = search.value.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
    let visible = 0;
    for (const card of cards) {
      const show = (topic.value === "all" || topic.value === card.dataset.topic)
        && terms.every(term => index.get(card).includes(term));
      card.hidden = !show;
      visible += Number(show);
    }
    count.textContent = `${visible} of ${cards.length} projects and experiments`;
    empty.hidden = visible !== 0;
    const url = new URL(window.location.href);
    for (const [key, value] of [["q", search.value.trim()], ["topic", topic.value]]) {
      if (value && value !== "all") url.searchParams.set(key, value);
      else url.searchParams.delete(key);
    }
    url.searchParams.delete("status");
    window.history.replaceState(null, "", url);
  }

  function reset() {
    clearTimeout(timer);
    search.value = "";
    topic.value = "all";
    filter();
  }

  function revealAnchor() {
    const target = cards.find(card => `#${card.id}` === window.location.hash);
    if (target && target.hidden) {
      reset();
      target.scrollIntoView({block: "start"});
    }
  }

  const params = new URLSearchParams(window.location.search);
  search.value = (params.get("q") || "").slice(0, 300);
  for (const select of [topic]) {
    const value = params.get(select.name);
    if ([...select.options].some(option => option.value === value)) select.value = value;
  }
  form.hidden = false;
  form.addEventListener("submit", event => { event.preventDefault(); clearTimeout(timer); filter(); });
  search.addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(filter, 120); });
  topic.addEventListener("change", filter);
  form.addEventListener("reset", event => { event.preventDefault(); reset(); search.focus(); });
  document.querySelector("#empty-reset").addEventListener("click", () => { reset(); search.focus(); });
  window.addEventListener("hashchange", revealAnchor);
  filter();
  revealAnchor();
})();
