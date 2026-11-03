// bend-frp's web runtime. An app (Web.bend) is two defs: init() and
// step(state, input). This file turns the page's events and the effects'
// answers into timed inputs, one at a time, calls step, compares the view
// with the last one and patches the DOM. It holds no state of the app's.
//
// Values cross as Bend's JS target has them: a constructor is
// {$: "Name", field: value}, a String is a JS string, a pair {fst, snd}.

const each = (xs, f) => {
  for (; xs.$ === "Con"; xs = xs.tail) f(xs.head);
};

const list = (xs) => {
  const out = [];
  each(xs, (x) => out.push(x));
  return out;
};

// Set as properties, since the attribute only gives the first value.
const PROPS = new Set(["value", "checked", "disabled", "selected"]);

// What an event carries: an input's text, a key with its modifiers, else "".
const keyOf = (e) =>
  (e.ctrlKey ? "C-" : "") + (e.altKey ? "M-" : "") + (e.shiftKey ? "S-" : "") + e.key;

const carried = (e) => {
  if (e.type === "keydown" || e.type === "keyup") return keyOf(e);
  const t = e.target;
  if (t && "value" in t) return String(t.value);
  return "";
};

export function mount(App, root, host = (globalThis.bendFrp ??= {})) {
  let state = App.init();
  let view = null;
  let node = null;
  const queue = [];
  let busy = false;

  const fire = (tag, value) => {
    queue.push({ $: "Input", at: Math.floor(performance.now()) >>> 0, tag, value });
    if (busy) return;
    busy = true;
    try {
      while (queue.length) {
        const r = App.step(state, queue.shift());
        state = r.fst;
        node = patch(root, node, view, r.snd.view);
        view = r.snd.view;
        each(r.snd.effects, perform);
      }
    } finally {
      busy = false;
    }
  };

  const perform = (fx) => {
    if (fx.$ === "Http") {
      const opts = { method: fx.method, credentials: "same-origin" };
      if (fx.method !== "GET" && fx.method !== "HEAD") {
        opts.body = fx.body;
        opts.headers = { "Content-Type": "application/json" };
      }
      fetch(fx.url, opts).then(
        async (a) => fire(a.ok ? fx.tag : fx.tag + ":failed", await a.text()),
        (e) => fire(fx.tag + ":failed", String(e)),
      );
    } else if (fx.$ === "After") {
      setTimeout(() => fire(fx.tag, ""), fx.ms);
    } else if (fx.$ === "Focus") {
      document.getElementById(fx.id)?.focus();
    } else if (fx.$ === "Host") {
      const a = host[fx.name]?.(fx.arg, (v) => fire(fx.tag, String(v)));
      if (typeof a === "string") queue.push({ $: "Input", at: 0, tag: fx.tag, value: a });
    }
  };

  // The handlers of an element live on it; one listener per event type reads
  // them, so a changed tag costs no listener.
  const listen = (dom, attrs) => {
    const on = (dom.__on ??= {});
    const seen = new Set();
    const keys = {};
    each(attrs, (a) => {
      if (a.$ === "OnKey") keys[a.key] = a.tag;
      if (a.$ !== "On" && a.$ !== "OnStop") return;
      seen.add(a.event);
      if (!(a.event in on)) {
        dom.addEventListener(a.event, (e) => {
          const h = on[a.event];
          if (!h) return;
          if (h.stop) e.preventDefault();
          fire(h.tag, carried(e));
        });
      }
      on[a.event] = { tag: a.tag, stop: a.$ === "OnStop" };
    });
    for (const k in on) if (!seen.has(k)) on[k] = null;
    if (Object.keys(keys).length && !dom.__keys) {
      dom.addEventListener("keydown", (e) => {
        const tag = dom.__keys[keyOf(e)];
        if (tag === undefined) return;
        e.preventDefault();
        fire(tag, "");
      });
    }
    dom.__keys = keys;
  };

  const setAttrs = (dom, attrs) => {
    const want = new Map();
    each(attrs, (a) => {
      if (a.$ === "Prop") want.set(a.name, a.value);
    });
    for (const name of dom.__attrs ?? []) {
      if (want.has(name)) continue;
      if (PROPS.has(name)) dom[name] = name === "value" ? "" : false;
      else dom.removeAttribute(name);
    }
    for (const [name, value] of want) {
      if (name === "checked" || name === "disabled" || name === "selected") {
        dom[name] = value !== "" && value !== "false";
      } else if (name === "value") {
        if (dom.value !== value) dom.value = value;
      } else if (dom.getAttribute(name) !== value) {
        dom.setAttribute(name, value);
      }
    }
    dom.__attrs = [...want.keys()];
    listen(dom, attrs);
  };

  const create = (v) => {
    if (v.$ === "HText") return document.createTextNode(v.s);
    const dom = document.createElement(v.tag);
    setAttrs(dom, v.attrs);
    if (v.$ === "HRaw") dom.innerHTML = v.html;
    else each(v.kids, (k) => dom.appendChild(create(k)));
    return dom;
  };

  const same = (a, b) => a.$ === b.$ && a.tag === b.tag && a.key === b.key;

  const update = (dom, old, v) => {
    if (v.$ === "HText") {
      if (old.s !== v.s) dom.nodeValue = v.s;
      return;
    }
    setAttrs(dom, v.attrs);
    if (v.$ === "HRaw") {
      if (old.html !== v.html) dom.innerHTML = v.html;
    } else {
      updateKids(dom, list(old.kids), list(v.kids));
    }
  };

  // Children: by key where they have one (moved, not rebuilt), else by place.
  const updateKids = (dom, olds, news) => {
    const doms = [...dom.childNodes];
    const byKey = new Map();
    olds.forEach((o, i) => {
      if (o.key) byKey.set(o.key, i);
    });
    const used = new Array(olds.length).fill(false);
    let place = 0;
    let cursor = dom.firstChild;
    news.forEach((n, j) => {
      let i = -1;
      if (n.key) {
        const at = byKey.get(n.key);
        if (at !== undefined && !used[at] && same(olds[at], n)) i = at;
      } else {
        while (place < olds.length && (used[place] || olds[place].key)) place++;
        if (place < olds.length && same(olds[place], n)) i = place;
      }
      if (i >= 0) {
        used[i] = true;
        update(doms[i], olds[i], n);
        if (doms[i] === cursor) cursor = cursor.nextSibling;
        else dom.insertBefore(doms[i], cursor);
      } else {
        dom.insertBefore(create(n), cursor);
      }
    });
    olds.forEach((_, i) => {
      if (!used[i]) dom.removeChild(doms[i]);
    });
  };

  const patch = (parent, dom, old, v) => {
    if (old && same(old, v)) {
      update(dom, old, v);
      return dom;
    }
    const fresh = create(v);
    if (dom) parent.replaceChild(fresh, dom);
    else parent.appendChild(fresh);
    return fresh;
  };

  fire("start", "");
  return { fire };
}
