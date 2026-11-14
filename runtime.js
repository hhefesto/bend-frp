// bend-frp's web runtime. An app (Web.bend) is two defs: init() and
// step(state, input). This file turns the page's events and the effects'
// answers into timed inputs, one at a time, calls step, and does to the DOM
// what Web.bend's diff of the last view and the new one says. It holds no
// state of the app's.
//
// Values cross as Bend's JS target has them: a constructor is
// {$: "Name", field: value}, a String is a JS string, a pair {fst, snd}.
import W from "./Web.bend";

const each = (xs, f) => {
  for (; xs.$ === "Con"; xs = xs.tail) f(xs.head);
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

  // Open sockets by tag; the tags told of the page's address.
  const sockets = {};
  const routes = [];
  const here = () => location.pathname + location.search + location.hash;
  const routed = () => routes.forEach((tag) => fire(tag, here()));
  globalThis.addEventListener?.("popstate", routed);

  // An input's time: the clock, read here and made a Time by Web.bend's
  // stamp, which keeps it after the last input's: no two inputs share a time.
  let last = { $: "Time", sec: 0, frac: 0 };
  const stamp = () => {
    const now = performance.now();
    const s = Math.floor(now / 1000);
    const ms = Math.floor(now - s * 1000);
    const sub = Math.floor((now - s * 1000 - ms) * 4294967296);
    last = W.stamp(last, s >>> 0, Math.min(ms, 999), sub >>> 0);
    return last;
  };

  const fire = (tag, value) => {
    queue.push({ $: "Input", at: stamp(), tag, value });
    if (busy) return;
    busy = true;
    try {
      while (queue.length) {
        const r = App.step(state, queue.shift());
        state = r.fst;
        node = view ? walk(node, W.diff(view, r.snd.view)) : root.appendChild(create(r.snd.view));
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
      if (typeof a === "string") queue.push({ $: "Input", at: stamp(), tag: fx.tag, value: a });
    } else if (fx.$ === "WsOpen") {
      const ws = new WebSocket(fx.url);
      sockets[fx.tag] = ws;
      ws.onopen = () => fire(fx.tag + ":open", "");
      ws.onmessage = (m) => fire(fx.tag, String(m.data));
      ws.onclose = () => {
        delete sockets[fx.tag];
        fire(fx.tag + ":closed", "");
      };
    } else if (fx.$ === "WsSend") {
      sockets[fx.tag]?.send(fx.data);
    } else if (fx.$ === "WsClose") {
      sockets[fx.tag]?.close();
    } else if (fx.$ === "Route") {
      routes.push(fx.tag);
      queue.push({ $: "Input", at: stamp(), tag: fx.tag, value: here() });
    } else if (fx.$ === "Navigate") {
      history.pushState(null, "", fx.url);
      routed();
    } else if (fx.$ === "StoreSet") {
      localStorage.setItem(fx.key, fx.value);
    } else if (fx.$ === "StoreGet") {
      queue.push({ $: "Input", at: stamp(), tag: fx.tag, value: localStorage.getItem(fx.key) ?? "" });
    } else if (fx.$ === "StoreDel") {
      localStorage.removeItem(fx.key);
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

  // Only what the view changed is written: the page's own scripts may keep
  // attributes of their own on an element, as `class` or `hidden` may change
  // under them, and a view that says the same thing leaves those alone.
  const setAttrs = (dom, attrs) => {
    const want = new Map();
    each(attrs, (a) => {
      if (a.$ === "Prop") want.set(a.name, a.value);
      if (a.$ === "Once" && !dom.__attrs) dom.setAttribute(a.name, a.value);
    });
    const had = dom.__attrs ?? new Map();
    for (const name of had.keys()) {
      if (want.has(name)) continue;
      if (PROPS.has(name)) dom[name] = name === "value" ? "" : false;
      else dom.removeAttribute(name);
    }
    for (const [name, value] of want) {
      if (name === "checked" || name === "disabled" || name === "selected") {
        if (had.get(name) !== value) dom[name] = value !== "" && value !== "false";
      } else if (name === "value") {
        if (dom.value !== value) dom.value = value;
      } else if (had.get(name) !== value) {
        dom.setAttribute(name, value);
      }
    }
    dom.__attrs = want;
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

  // Do what Web.bend's diff says (it is proved to make the last view the new
  // one), an edit at a time; answer the node now in dom's place.
  const walk = (dom, e) => {
    if (e.$ === "EKeep") return dom;
    if (e.$ === "ESwap") {
      const fresh = create(e.node);
      dom.parentNode.replaceChild(fresh, dom);
      return fresh;
    }
    if (e.$ === "EText") {
      dom.nodeValue = e.s;
      return dom;
    }
    if (e.attrs.$ === "Some") setAttrs(dom, e.attrs.value);
    if (e.$ === "ERaw") {
      if (e.html.$ === "Some") dom.innerHTML = e.html.value;
      return dom;
    }
    const doms = [...dom.childNodes];
    let i = 0;
    each(e.kids, (k) => {
      if (k.$ === "KDrop") dom.removeChild(doms[i++]);
      else if (k.$ === "KAdd") dom.appendChild(create(k.node));
      else walk(doms[i++], k.edit);
    });
    return dom;
  };

  fire("start", "");
  return { fire };
}
