// Hall Defenders v2 — kingdom co-op.
// P1 Builder: arrows (+shift = fast) move cursor, Y/U/I/O tools, Enter build, Del sell, P hire miner.
// P2 Hero: WASD move, Shift dash (stamina), mouse aim, Space punch, E enter portal / buy pistol.
// Starts bare-handed and slower than wolves — dash to survive. Gold comes from the mines.
// Buildings cost wood/stone. Portals open in the wild (Solo Leveling style): clear the arena
// inside before the timer runs out, or the portal breaks and its monsters charge the hall.
(() => {
'use strict';

const SPR = window.SPR;
const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
ctx.imageSmoothingEnabled = false;

// ---------------------------------------------------------------- constants
const TILE = 32;
const WT = 96, HT = 64;                    // world size in tiles
const WORLD_W = WT * TILE, WORLD_H = HT * TILE;
const W = canvas.width, H = canvas.height;
const HUD_H = 56;
const VIEW_H = H - HUD_H;
const LEFT_VX = 0, LEFT_VW = 637;
const RIGHT_VX = 643, RIGHT_VW = 637;

const T_GRASS = 0, T_FOREST = 1, T_MOUNTAIN = 2, T_DEPOSIT = 3;

const COSTS = {
  wall: { wood: 10 },
  turret: { stone: 25 },
  house: { wood: 20, stone: 10 },
};
const BUILDING_HP = { wall: 80, turret: 60, house: 50 };
const SELL_RATIO = 0.5;
const BUILD_RADIUS = 14;                   // tiles from hall center
const MINER_COST = 30;
const MINER_CARRY = 25;
const MINER_GATHER = 4;                    // gold per second while mining
const HALL_MAX_HP = 500;
const HERO_MAX_HP = 60;
const HERO_SPEED = 80;                     // slower than a chasing wolf (95)
const HERO_STAM_MAX = 100;
const HERO_DASH_COST = 30;
const HERO_DASH_SPEED = 460;
const HERO_DASH_TIME = 0.08;
const HERO_STAM_REGEN = 11;
const PISTOL_COST = 150;
const HERO_FIRE_CD = 0.18;
const HERO_BULLET_DMG = 7;
const MELEE_DMG = 12;
const MELEE_CD = 0.45;
const MELEE_RANGE = 46;
const RESPAWN_TIME = 5;
const WOOD_PER_SEC = 0.6;
const STONE_PER_SEC = 0.35;
const MEAT_PER_SEC = 0.15;
const REVIVE_MEAT_COST = 10;
const FIRST_PORTAL_AT = 100;
const PORTAL_BREAK_TIME = 75;
const ARENA_WT = 20, ARENA_HT = 18;
const ARENA_W = ARENA_WT * TILE, ARENA_H = ARENA_HT * TILE;
const ARENA_PAD = TILE + 12;               // keep actors off the arena walls
const TURRET_RANGE = 150;
const TURRET_CD = 0.7;
const TURRET_DMG = 8;
const HOUSE_TAX_EVERY = 6;
const DANGER_RADIUS = 170;                 // monsters this close scare miners

// ---------------------------------------------------------------- state
let state = 'title';
let time, gold, wood, stone, meat, portalLevel, portalT, portals;
let terrain, revealed, bgrid;
let deposits, dens, enemies, miners, bullets, effects, floaters, announcements;
let hall, hero, cursor, builderCam, heroCam;
let heroTileX = -1, heroTileY = -1;
let minimapT = 0;
const minimap = document.createElement('canvas');
minimap.width = WT; minimap.height = HT;

const idx = (tx, ty) => ty * WT + tx;
const inWorld = (tx, ty) => tx >= 0 && ty >= 0 && tx < WT && ty < HT;

// ---------------------------------------------------------------- world gen
function hash2(x, y, seed) {
  let h = x * 374761393 + y * 668265263 + seed * 1442695040888963407;
  h = (h ^ (h >> 13)) * 1274126177;
  return ((h ^ (h >> 16)) >>> 0) / 4294967295;
}
function smooth(t) { return t * t * (3 - 2 * t); }
function noise(x, y, seed) {
  const x0 = Math.floor(x), y0 = Math.floor(y);
  const fx = smooth(x - x0), fy = smooth(y - y0);
  const a = hash2(x0, y0, seed), b = hash2(x0 + 1, y0, seed);
  const c = hash2(x0, y0 + 1, seed), d = hash2(x0 + 1, y0 + 1, seed);
  return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
}

function newGame() {
  time = 0; gold = 100; wood = 0; stone = 0; meat = REVIVE_MEAT_COST;
  portalLevel = 0; portalT = FIRST_PORTAL_AT; portals = [];
  deposits = []; dens = []; enemies = []; miners = [];
  bullets = []; effects = []; floaters = []; announcements = [];
  terrain = new Uint8Array(WT * HT);
  revealed = new Uint8Array(WT * HT);
  bgrid = new Array(WT * HT).fill(null);

  hall = { kind: 'hall', hp: HALL_MAX_HP, maxHp: HALL_MAX_HP, tx: 47, ty: 31 };
  const hcx = hallCX(), hcy = hallCY();
  const seed = Math.floor(Math.random() * 1e9);

  for (let ty = 0; ty < HT; ty++) {
    for (let tx = 0; tx < WT; tx++) {
      const d = Math.hypot(tx + 0.5 - (hall.tx + 1), ty + 0.5 - (hall.ty + 1));
      if (d < 15) continue;                       // city zone stays open grass
      const n = noise(tx / 8, ty / 8, seed);
      if (n > 0.72) terrain[idx(tx, ty)] = T_MOUNTAIN;
      else if (n > 0.60) terrain[idx(tx, ty)] = T_FOREST;
    }
  }
  // keep the map border walkable so nothing spawns sealed in a corner
  for (let tx = 0; tx < WT; tx++) { terrain[idx(tx, 0)] = 0; terrain[idx(tx, HT - 1)] = 0; }
  for (let ty = 0; ty < HT; ty++) { terrain[idx(0, ty)] = 0; terrain[idx(WT - 1, ty)] = 0; }

  for (let dy = 0; dy < 2; dy++)
    for (let dx = 0; dx < 2; dx++)
      bgrid[idx(hall.tx + dx, hall.ty + dy)] = hall;

  // gold deposits ring the map, each guarded by a wolf den
  let placed = 0, tries = 0;
  while (placed < 10 && tries < 400) {
    tries++;
    const ang = Math.random() * Math.PI * 2;
    const dist = 22 + Math.random() * 20;
    const tx = Math.round(hall.tx + 1 + Math.cos(ang) * dist);
    const ty = Math.round(hall.ty + 1 + Math.sin(ang) * dist * 0.66);
    if (!inWorld(tx, ty) || tx < 3 || ty < 3 || tx > WT - 4 || ty > HT - 4) continue;
    if (terrain[idx(tx, ty)] !== T_GRASS || bgrid[idx(tx, ty)]) continue;
    if (deposits.some((dp) => Math.hypot(dp.tx - tx, dp.ty - ty) < 8)) continue;
    terrain[idx(tx, ty)] = T_DEPOSIT;
    deposits.push({ tx, ty, amount: Math.round(160 + dist * 4), discovered: false });
    // den nearby
    for (let dt = 0; dt < 20; dt++) {
      const dx2 = tx + Math.round((Math.random() - 0.5) * 6);
      const dy2 = ty + Math.round((Math.random() - 0.5) * 6);
      if (!inWorld(dx2, dy2) || terrain[idx(dx2, dy2)] !== T_GRASS) continue;
      if (Math.hypot(dx2 - tx, dy2 - ty) < 2) continue;
      const den = { x: (dx2 + 0.5) * TILE, y: (dy2 + 0.5) * TILE, hp: 60, maxHp: 60, spawnT: 5 };
      dens.push(den);
      const wolves = 2 + Math.floor(dist / 14);
      for (let i = 0; i < wolves; i++) spawnWolf(den);
      break;
    }
    placed++;
  }

  hero = {
    x: hcx, y: hcy + 2.2 * TILE, hp: HERO_MAX_HP, r: 10, aim: 0,
    fireCd: 0, meleeCd: 0, dead: false, respawn: 0,
    stam: HERO_STAM_MAX, dashT: 0, dashX: 0, dashY: 0, hasGun: false,
    arena: null, retX: hcx, retY: hcy,
  };
  cursor = { tx: hall.tx - 3, ty: hall.ty, tool: 'wall' };
  builderCam = { x: hcx - LEFT_VW / 2, y: hcy - VIEW_H / 2 };
  heroCam = { x: hcx - RIGHT_VW / 2, y: hcy - VIEW_H / 2 };
  heroTileX = -1; heroTileY = -1;

  revealCircle(hall.tx + 1, hall.ty + 1, 16);
}

function hallCX() { return (hall.tx + 1) * TILE; }
function hallCY() { return (hall.ty + 1) * TILE; }

function spawnWolf(den) {
  enemies.push({
    ai: 'wolf', spr: 'wolf', den,
    x: den.x + (Math.random() - 0.5) * 80, y: den.y + (Math.random() - 0.5) * 80,
    home: { x: den.x, y: den.y },
    r: 9, hp: 24, maxHp: 24, dmg: 8, atkCd: 0,
    wt: 0, wx: den.x, wy: den.y,
  });
}

// ---------------------------------------------------------------- fog
function revealCircle(ctx_, cty, radius) {
  for (let ty = Math.max(0, cty - radius); ty <= Math.min(HT - 1, cty + radius); ty++) {
    for (let tx = Math.max(0, ctx_ - radius); tx <= Math.min(WT - 1, ctx_ + radius); tx++) {
      if (Math.hypot(tx - ctx_, ty - cty) > radius) continue;
      const i = idx(tx, ty);
      if (revealed[i]) continue;
      revealed[i] = 1;
      if (terrain[i] === T_DEPOSIT) {
        const dp = deposits.find((d) => d.tx === tx && d.ty === ty);
        if (dp && !dp.discovered) {
          dp.discovered = true;
          announce('gold deposit discovered! (see minimap)', '#e8c83a');
        }
      }
    }
  }
}

// ---------------------------------------------------------------- solidity
function tileSolid(tx, ty, ignoreBuildings) {
  if (!inWorld(tx, ty)) return true;
  const t = terrain[idx(tx, ty)];
  if (t === T_MOUNTAIN || t === T_DEPOSIT) return true;
  if (!ignoreBuildings && bgrid[idx(tx, ty)]) return true;
  return false;
}
function solidAt(x, y) {
  if (x < 0 || y < 0 || x >= WORLD_W || y >= WORLD_H) return true;
  return tileSolid(Math.floor(x / TILE), Math.floor(y / TILE), false);
}

// slide movement; returns the building that blocked us (if any)
function moveActor(a, dx, dy) {
  let blocked = null;
  const probe = (nx, ny) => {
    for (const [ox, oy] of [[-a.r, 0], [a.r, 0], [0, -a.r], [0, a.r]]) {
      if (solidAt(nx + ox, ny + oy)) {
        const tx = Math.floor((nx + ox) / TILE), ty = Math.floor((ny + oy) / TILE);
        if (inWorld(tx, ty) && bgrid[idx(tx, ty)]) blocked = bgrid[idx(tx, ty)];
        return true;
      }
    }
    return false;
  };
  if (dx !== 0 && !probe(a.x + dx, a.y)) a.x += dx;
  if (dy !== 0 && !probe(a.x, a.y + dy)) a.y += dy;
  return blocked;
}

// ---------------------------------------------------------------- A* pathfinding
function findPath(sx, sy, tx, ty, ignoreBuildings) {
  if (!inWorld(sx, sy) || !inWorld(tx, ty)) return null;
  const goal = idx(tx, ty);
  const g = new Map(), came = new Map();
  const heap = [];                            // [f, tileIndex]
  const push = (f, i) => {
    heap.push([f, i]);
    let c = heap.length - 1;
    while (c > 0) {
      const p = (c - 1) >> 1;
      if (heap[p][0] <= heap[c][0]) break;
      [heap[p], heap[c]] = [heap[c], heap[p]];
      c = p;
    }
  };
  const pop = () => {
    const top = heap[0], last = heap.pop();
    if (heap.length) {
      heap[0] = last;
      let c = 0;
      for (;;) {
        let m = c;
        const l = c * 2 + 1, r = c * 2 + 2;
        if (l < heap.length && heap[l][0] < heap[m][0]) m = l;
        if (r < heap.length && heap[r][0] < heap[m][0]) m = r;
        if (m === c) break;
        [heap[m], heap[c]] = [heap[c], heap[m]];
        c = m;
      }
    }
    return top;
  };
  const hcost = (i) => Math.abs((i % WT) - tx) + Math.abs(Math.floor(i / WT) - ty);

  const start = idx(sx, sy);
  g.set(start, 0);
  push(hcost(start), start);
  let expansions = 0;

  while (heap.length && expansions < 3500) {
    const [, cur] = pop();
    expansions++;
    if (cur === goal) {
      const path = [];
      let n = cur;
      while (n !== undefined && n !== start) {
        path.push({ x: ((n % WT) + 0.5) * TILE, y: (Math.floor(n / WT) + 0.5) * TILE });
        n = came.get(n);
      }
      path.reverse();
      return path;
    }
    const cx = cur % WT, cy = Math.floor(cur / WT);
    const gc = g.get(cur);
    for (const [nx, ny] of [[cx + 1, cy], [cx - 1, cy], [cx, cy + 1], [cx, cy - 1]]) {
      if (!inWorld(nx, ny)) continue;
      const ni = idx(nx, ny);
      if (ni !== goal && tileSolid(nx, ny, ignoreBuildings)) continue;
      const ng = gc + 1;
      if (g.has(ni) && g.get(ni) <= ng) continue;
      g.set(ni, ng);
      came.set(ni, cur);
      push(ng + hcost(ni), ni);
    }
  }
  return null;
}

// follow a path of waypoints; returns blocking building if physically stuck against one
function followPath(a, speed, dt) {
  if (!a.path || a.pathIdx >= a.path.length) return null;
  const wp = a.path[a.pathIdx];
  const d = Math.hypot(wp.x - a.x, wp.y - a.y);
  if (d < 8) { a.pathIdx++; return null; }
  const blocked = moveActor(a, ((wp.x - a.x) / d) * speed * dt, ((wp.y - a.y) / d) * speed * dt);
  return blocked;
}

function setPathTo(a, tx, ty, ignoreBuildings) {
  const stx = Math.floor(a.x / TILE), sty = Math.floor(a.y / TILE);
  a.path = findPath(stx, sty, tx, ty, ignoreBuildings);
  a.pathIdx = 0;
}

// ---------------------------------------------------------------- input
const keys = {};
let dashRequest = false;
const mouse = { x: W / 2, y: H / 2, down: false };
const TOOL_KEYS = { KeyY: 'wall', KeyU: 'turret', KeyI: 'house', KeyO: 'repair' };

window.addEventListener('keydown', (e) => {
  if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space', 'Backspace'].includes(e.code)) e.preventDefault();
  keys[e.code] = true;

  if (state === 'title' && (e.code === 'Enter' || e.code === 'Space')) { state = 'play'; return; }
  if (state === 'over' && e.code === 'KeyR') { newGame(); state = 'play'; return; }
  if (state !== 'play') return;

  const step = e.shiftKey ? 5 : 1;
  if (e.code === 'ArrowUp')    cursor.ty = Math.max(0, cursor.ty - step);
  if (e.code === 'ArrowDown')  cursor.ty = Math.min(HT - 1, cursor.ty + step);
  if (e.code === 'ArrowLeft')  cursor.tx = Math.max(0, cursor.tx - step);
  if (e.code === 'ArrowRight') cursor.tx = Math.min(WT - 1, cursor.tx + step);
  if (TOOL_KEYS[e.code]) cursor.tool = TOOL_KEYS[e.code];
  if (e.code === 'Enter') builderAction();
  if (e.code === 'Delete' || e.code === 'Backspace') sellAt(cursor.tx, cursor.ty);
  if (e.code === 'KeyP') hireMiner();
  if ((e.code === 'ShiftLeft' || e.code === 'ShiftRight') && !e.repeat) dashRequest = true;
  if (e.code === 'KeyE') { if (!tryEnterPortal()) buyPistol(); }
});
window.addEventListener('keyup', (e) => { keys[e.code] = false; });

canvas.addEventListener('mousemove', (e) => {
  const r = canvas.getBoundingClientRect();
  mouse.x = (e.clientX - r.left) * (W / r.width);
  mouse.y = (e.clientY - r.top) * (H / r.height);
});
canvas.addEventListener('mousedown', () => {
  mouse.down = true;
  if (state === 'title') state = 'play';
});
window.addEventListener('mouseup', () => { mouse.down = false; });
canvas.addEventListener('contextmenu', (e) => e.preventDefault());

// ---------------------------------------------------------------- resources
function canAfford(cost) {
  return gold >= (cost.gold || 0) && wood >= (cost.wood || 0)
    && stone >= (cost.stone || 0) && meat >= (cost.meat || 0);
}
function payCost(cost) {
  gold -= cost.gold || 0; wood -= cost.wood || 0;
  stone -= cost.stone || 0; meat -= cost.meat || 0;
}
function costText(cost) {
  const parts = [];
  if (cost.gold) parts.push(`${cost.gold}g`);
  if (cost.wood) parts.push(`${cost.wood}w`);
  if (cost.stone) parts.push(`${cost.stone}s`);
  if (cost.meat) parts.push(`${cost.meat}m`);
  return parts.join('+');
}

// ---------------------------------------------------------------- builder
function canBuildAt(tx, ty) {
  if (!inWorld(tx, ty)) return false;
  if (Math.hypot(tx + 0.5 - (hall.tx + 1), ty + 0.5 - (hall.ty + 1)) > BUILD_RADIUS) return false;
  const t = terrain[idx(tx, ty)];
  if (t === T_MOUNTAIN || t === T_DEPOSIT) return false;
  if (bgrid[idx(tx, ty)]) return false;
  return true;
}

function builderAction() {
  const { tx, ty, tool } = cursor;
  const existing = inWorld(tx, ty) ? bgrid[idx(tx, ty)] : null;

  if (tool === 'repair') {
    if (!existing || existing.hp >= existing.maxHp) return;
    const cost = Math.ceil((existing.maxHp - existing.hp) / 5);
    if (gold < cost) { addFloater(tx * TILE, ty * TILE, 'need gold!', '#e05050'); return; }
    gold -= cost;
    existing.hp = existing.maxHp;
    addFloater(tx * TILE, ty * TILE, 'repaired', '#50d060');
    return;
  }

  if (!canBuildAt(tx, ty)) return;
  const cost = COSTS[tool];
  if (!canAfford(cost)) { addFloater(tx * TILE, ty * TILE, 'need resources!', '#e05050'); return; }
  const cx = (tx + 0.5) * TILE, cy = (ty + 0.5) * TILE;
  if (!hero.dead && !hero.arena && Math.hypot(hero.x - cx, hero.y - cy) < TILE) return;
  if (enemies.some((en) => Math.hypot(en.x - cx, en.y - cy) < TILE)) return;
  if (miners.some((m) => Math.hypot(m.x - cx, m.y - cy) < TILE)) return;

  payCost(cost);
  if (terrain[idx(tx, ty)] === T_FOREST) terrain[idx(tx, ty)] = T_GRASS;
  const hp = BUILDING_HP[tool];
  bgrid[idx(tx, ty)] = { kind: tool, hp, maxHp: hp, tx, ty, cd: 0, angle: 0, incomeTimer: 0 };
}

function sellAt(tx, ty) {
  if (!inWorld(tx, ty)) return;
  const b = bgrid[idx(tx, ty)];
  if (!b || b.kind === 'hall') return;
  const back = {};
  for (const [k, v] of Object.entries(COSTS[b.kind])) back[k] = Math.floor(v * SELL_RATIO);
  gold += back.gold || 0; wood += back.wood || 0;
  stone += back.stone || 0; meat += back.meat || 0;
  bgrid[idx(tx, ty)] = null;
  addFloater(tx * TILE, ty * TILE, `+${costText(back)}`, '#e8c83a');
}

function destroyBuilding(b) {
  if (b.kind === 'hall') { state = 'over'; return; }
  bgrid[idx(b.tx, b.ty)] = null;
  addEffect((b.tx + 0.5) * TILE, (b.ty + 0.5) * TILE, 'boom');
}

function countHouses() {
  let n = 0;
  for (const b of bgrid) if (b && b.kind === 'house' && b !== hall) n++;
  return n;
}
function minerCap() { return 2 + countHouses() * 2; }

function hireMiner() {
  if (miners.length >= minerCap()) { announce('build houses to hire more miners', '#e05050'); return; }
  if (gold < MINER_COST) { announce('not enough gold to hire a miner', '#e05050'); return; }
  gold -= MINER_COST;
  miners.push({
    x: hallCX() + (Math.random() - 0.5) * 40, y: hallCY() + 2.2 * TILE,
    r: 8, hp: 30, maxHp: 30, state: 'idle', carry: 0, deposit: null,
    path: null, pathIdx: 0, stuckT: 0, lastX: 0, lastY: 0,
  });
  announce('miner hired — the hero can escort them (they follow him)', '#80d0ff');
}

function buyPistol() {
  if (state !== 'play' || hero.dead || hero.arena || hero.hasGun) return;
  if (Math.hypot(hero.x - hallCX(), hero.y - hallCY()) > 100) {
    announce('the pistol is sold at the hall — get closer', '#e05050');
    return;
  }
  if (gold < PISTOL_COST) {
    announce(`the pistol costs ${PISTOL_COST}g — mine more gold`, '#e05050');
    return;
  }
  gold -= PISTOL_COST;
  hero.hasGun = true;
  addFloater(hero.x, hero.y - 16, 'pistol!', '#ffe080');
  announce('pistol purchased! click to shoot', '#80d0ff');
}

// ---------------------------------------------------------------- portals
// Portals open in the wild. Enter one (E) to fight its monsters in an arena;
// clear it for loot. If its timer runs out, it breaks and the monsters charge the hall.
function arenaWolf(isBoss, level, i) {
  if (isBoss) {
    const hp = 120 + level * 30;
    return { spr: 'wolf', isBoss: true, size: 52, r: 15, hp, maxHp: hp, dmg: 16, speed: 72,
      atkCd: 0, x: ARENA_W / 2, y: 2.5 * TILE };
  }
  const hp = 24 + level * 4;
  return { spr: 'wolf', isBoss: false, size: 26, r: 9, hp, maxHp: hp, dmg: 8, speed: 95,
    atkCd: 0,
    x: TILE * 3 + (i % 5) * ((ARENA_W - TILE * 6) / 4),
    y: TILE * (4 + Math.floor(i / 5) * 2) };
}

function spawnPortal() {
  portalLevel++;
  for (let t = 0; t < 80; t++) {
    const ang = Math.random() * Math.PI * 2;
    const dist = 20 + Math.random() * 10;
    const tx = Math.round(hall.tx + 1 + Math.cos(ang) * dist);
    const ty = Math.round(hall.ty + 1 + Math.sin(ang) * dist * 0.66);
    if (!inWorld(tx, ty) || tileSolid(tx, ty, false)) continue;
    const dir = Math.abs(Math.cos(ang)) > Math.abs(Math.sin(ang))
      ? (Math.cos(ang) > 0 ? 'east' : 'west')
      : (Math.sin(ang) > 0 ? 'south' : 'north');
    const mobs = [];
    const wolves = 2 + portalLevel;
    for (let i = 0; i < wolves; i++) mobs.push(arenaWolf(false, portalLevel, i));
    mobs.push(arenaWolf(true, portalLevel, 0));
    portals.push({ x: (tx + 0.5) * TILE, y: (ty + 0.5) * TILE, color: 'green',
      t: PORTAL_BREAK_TIME, level: portalLevel, mobs });
    revealCircle(tx, ty, 3);
    announce(`a GREEN portal opened to the ${dir} — clear it before it breaks!`, '#40e080');
    return;
  }
}

function tryEnterPortal() {
  if (state !== 'play' || hero.dead || hero.arena) return false;
  for (const p of portals) {
    if (Math.hypot(p.x - hero.x, p.y - hero.y) < 40) {
      hero.arena = p;
      hero.retX = hero.x; hero.retY = hero.y;
      hero.x = ARENA_W / 2; hero.y = ARENA_H - 2 * TILE;
      heroCam.x = (ARENA_W - RIGHT_VW) / 2;
      heroCam.y = (ARENA_H - VIEW_H) / 2;
      announce('the hero entered the portal!', '#40e080');
      return true;
    }
  }
  return false;
}

function clearPortal(p) {
  const lootMeat = 12 + p.level * 3, lootWood = 10, lootStone = 8;
  meat += lootMeat; wood += lootWood; stone += lootStone;
  if (hero.arena === p) {
    hero.arena = null;
    hero.x = hero.retX; hero.y = hero.retY;
  }
  portals.splice(portals.indexOf(p), 1);
  announce(`portal cleared! +${lootMeat} meat +${lootWood} wood +${lootStone} stone`, '#40e080');
}

function breakPortal(p) {
  portals.splice(portals.indexOf(p), 1);
  for (const m of p.mobs) {
    enemies.push({
      ai: 'raider', spr: 'wolf', size: m.size, r: m.r, hp: m.hp, maxHp: m.maxHp,
      dmg: m.dmg, speed: m.isBoss ? 60 : 95,
      x: p.x + (Math.random() - 0.5) * 60, y: p.y + (Math.random() - 0.5) * 60,
      atkCd: 0, path: null, pathIdx: 0, repathT: 0,
    });
  }
  announce('a portal BROKE — its monsters are loose!', '#ff6060');
}

function updateArena(dt) {
  const p = hero.arena;
  for (const m of p.mobs) {
    m.atkCd -= dt;
    const d = Math.hypot(hero.x - m.x, hero.y - m.y);
    if (d > 1) {
      m.x += ((hero.x - m.x) / d) * m.speed * dt;
      m.y += ((hero.y - m.y) / d) * m.speed * dt;
    }
    for (const o of p.mobs) {
      if (o === m) continue;
      const od = Math.hypot(o.x - m.x, o.y - m.y);
      if (od > 0 && od < m.r + o.r) {
        m.x -= ((o.x - m.x) / od) * 14 * dt;
        m.y -= ((o.y - m.y) / od) * 14 * dt;
      }
    }
    m.x = clamp(m.x, ARENA_PAD, ARENA_W - ARENA_PAD);
    m.y = clamp(m.y, ARENA_PAD, ARENA_H - ARENA_PAD);
    if (m.atkCd <= 0 && d < m.r + hero.r + 5) {
      m.atkCd = 0.9;
      hero.hp -= m.dmg;
      addEffect(hero.x, hero.y, 'hit', 0, p);
      if (hero.hp <= 0) {
        hero.dead = true; hero.respawn = RESPAWN_TIME;
        hero.arena = null;
        announce('the hero fell inside the portal!', '#ff6060');
        return;
      }
    }
  }
  p.mobs = p.mobs.filter((m) => m.hp > 0);
  if (p.mobs.length === 0) clearPortal(p);
}

// ---------------------------------------------------------------- update
function update(dt) {
  time += dt;

  wood += WOOD_PER_SEC * dt;
  stone += STONE_PER_SEC * dt;
  meat += MEAT_PER_SEC * dt;

  portalT -= dt;
  if (portalT <= 0) {
    spawnPortal();
    portalT = Math.max(50, 95 - portalLevel * 5);
  }
  for (let i = portals.length - 1; i >= 0; i--) {
    const p = portals[i];
    if (hero.arena === p) continue;            // timer pauses while the hero fights inside
    p.t -= dt;
    if (p.t <= 0) breakPortal(p);
  }

  updateHero(dt);
  if (hero.arena && !hero.dead) updateArena(dt);
  updateMiners(dt);
  updateEnemies(dt);
  updateDens(dt);
  updateBuildings(dt);
  updateBullets(dt);

  for (const fx of effects) fx.life -= dt;
  effects = effects.filter((f) => f.life > 0);
  for (const fl of floaters) { fl.y -= 18 * dt; fl.life -= dt; }
  floaters = floaters.filter((f) => f.life > 0);
  for (const an of announcements) an.life -= dt;
  announcements = announcements.filter((a) => a.life > 0);

  // cameras
  const lerp = Math.min(1, 8 * dt);
  const btx = clamp((cursor.tx + 0.5) * TILE - LEFT_VW / 2, 0, WORLD_W - LEFT_VW);
  const bty = clamp((cursor.ty + 0.5) * TILE - VIEW_H / 2, 0, WORLD_H - VIEW_H);
  builderCam.x += (btx - builderCam.x) * lerp;
  builderCam.y += (bty - builderCam.y) * lerp;
  if (hero.arena) {
    heroCam.x = (ARENA_W - RIGHT_VW) / 2;
    heroCam.y = (ARENA_H - VIEW_H) / 2;
  } else {
    const htx = clamp(hero.x - RIGHT_VW / 2, 0, WORLD_W - RIGHT_VW);
    const hty = clamp(hero.y - VIEW_H / 2, 0, WORLD_H - VIEW_H);
    heroCam.x += (htx - heroCam.x) * lerp;
    heroCam.y += (hty - heroCam.y) * lerp;
  }

  minimapT -= dt;
  if (minimapT <= 0) { renderMinimapBase(); minimapT = 0.5; }
}

function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

function nearestDanger(x, y, radius) {
  let best = null, bd = radius;
  for (const en of enemies) {
    const d = Math.hypot(en.x - x, en.y - y);
    if (d < bd) { best = en; bd = d; }
  }
  return best;
}

function heroMove(dx, dy) {
  if (hero.arena) {
    hero.x = clamp(hero.x + dx, ARENA_PAD, ARENA_W - ARENA_PAD);
    hero.y = clamp(hero.y + dy, ARENA_PAD, ARENA_H - ARENA_PAD);
  } else {
    moveActor(hero, dx, dy);
  }
}

function updateHero(dt) {
  if (hero.dead) {
    dashRequest = false;
    hero.respawn -= dt;
    if (hero.respawn <= 0 && meat >= REVIVE_MEAT_COST) {
      meat -= REVIVE_MEAT_COST;
      hero.dead = false;
      hero.hp = HERO_MAX_HP;
      hero.stam = HERO_STAM_MAX;
      hero.dashT = 0;
      hero.x = hallCX(); hero.y = hallCY() + 2.2 * TILE;
      addFloater(hero.x, hero.y - 16, `-${REVIVE_MEAT_COST} meat`, '#e07070');
    }
    return;
  }
  hero.stam = Math.min(HERO_STAM_MAX, hero.stam + HERO_STAM_REGEN * dt);

  let mx = (keys.KeyD ? 1 : 0) - (keys.KeyA ? 1 : 0);
  let my = (keys.KeyS ? 1 : 0) - (keys.KeyW ? 1 : 0);
  if (dashRequest) {
    dashRequest = false;
    if (hero.dashT <= 0 && hero.stam >= HERO_DASH_COST && (mx || my)) {
      hero.stam -= HERO_DASH_COST;
      hero.dashT = HERO_DASH_TIME;
      const len = Math.hypot(mx, my);
      hero.dashX = mx / len; hero.dashY = my / len;
      addEffect(hero.x, hero.y, 'hit', 0, hero.arena);
    }
  }
  if (hero.dashT > 0) {
    hero.dashT -= dt;
    heroMove(hero.dashX * HERO_DASH_SPEED * dt, hero.dashY * HERO_DASH_SPEED * dt);
  } else if (mx || my) {
    const len = Math.hypot(mx, my);
    heroMove((mx / len) * HERO_SPEED * dt, (my / len) * HERO_SPEED * dt);
  }

  // fog reveal when crossing into a new tile
  if (!hero.arena) {
    const tx = Math.floor(hero.x / TILE), ty = Math.floor(hero.y / TILE);
    if (tx !== heroTileX || ty !== heroTileY) {
      heroTileX = tx; heroTileY = ty;
      revealCircle(tx, ty, 8);
    }
  }

  // aim at the mouse inside the hero viewport
  const aimX = heroCam.x + (clamp(mouse.x, RIGHT_VX, RIGHT_VX + RIGHT_VW) - RIGHT_VX);
  const aimY = heroCam.y + (clamp(mouse.y, HUD_H, H) - HUD_H);
  hero.aim = Math.atan2(aimY - hero.y, aimX - hero.x);

  hero.fireCd -= dt;
  if (hero.hasGun && mouse.down && hero.fireCd <= 0) {
    hero.fireCd = HERO_FIRE_CD;
    bullets.push({ x: hero.x + Math.cos(hero.aim) * 14, y: hero.y + Math.sin(hero.aim) * 14,
      vx: Math.cos(hero.aim) * 440, vy: Math.sin(hero.aim) * 440,
      dmg: HERO_BULLET_DMG, life: 0.9, hero: true, space: hero.arena });
  }

  hero.meleeCd -= dt;
  if (keys.Space && hero.meleeCd <= 0) {
    hero.meleeCd = MELEE_CD;
    addEffect(hero.x, hero.y, 'slash', hero.aim, hero.arena);
    const inArc = (x, y, r) => {
      const d = Math.hypot(x - hero.x, y - hero.y);
      if (d > MELEE_RANGE + r) return false;
      const angTo = Math.atan2(y - hero.y, x - hero.x);
      let diff = Math.abs(angTo - hero.aim);
      if (diff > Math.PI) diff = 2 * Math.PI - diff;
      return diff < Math.PI / 2;
    };
    const targets = hero.arena ? hero.arena.mobs : enemies;
    for (const en of targets) {
      if (!inArc(en.x, en.y, en.r)) continue;
      damageEnemy(en, MELEE_DMG, hero.arena);
      const angTo = Math.atan2(en.y - hero.y, en.x - hero.x);
      en.x += Math.cos(angTo) * 10;
      en.y += Math.sin(angTo) * 10;
    }
    if (!hero.arena) {
      for (const den of dens) {
        if (inArc(den.x, den.y, 16)) damageDen(den, MELEE_DMG);
      }
    }
  }

  // heal near the hall
  if (!hero.arena && Math.hypot(hero.x - hallCX(), hero.y - hallCY()) < 100 && hero.hp < HERO_MAX_HP) {
    hero.hp = Math.min(HERO_MAX_HP, hero.hp + 5 * dt);
  }
}

function updateMiners(dt) {
  const hx = hallCX(), hy = hallCY();
  for (let i = miners.length - 1; i >= 0; i--) {
    const m = miners[i];

    // stuck detection for anything path-driven
    const moved = Math.hypot(m.x - m.lastX, m.y - m.lastY);
    m.lastX = m.x; m.lastY = m.y;
    if (m.path && moved < 0.3) m.stuckT += dt; else m.stuckT = 0;

    const danger = nearestDanger(m.x, m.y, DANGER_RADIUS);

    if (m.state === 'idle') {
      if (!hero.dead && !hero.arena && Math.hypot(hero.x - m.x, hero.y - m.y) < 180) {
        m.state = 'follow';
        m.path = null;
      }
    } else if (m.state === 'follow') {
      if (hero.dead || hero.arena || Math.hypot(hero.x - m.x, hero.y - m.y) > 650) {
        goHome(m);
      } else {
        const ang = (i / Math.max(1, miners.length)) * Math.PI * 2;
        const tgtX = hero.x + Math.cos(ang) * 34, tgtY = hero.y + Math.sin(ang) * 34;
        const d = Math.hypot(tgtX - m.x, tgtY - m.y);
        if (m.path) {
          followPath(m, 120, dt);
          if (Math.hypot(hero.x - m.x, hero.y - m.y) < 70 || m.pathIdx >= m.path.length) m.path = null;
          if (m.stuckT > 1) { setPathTo(m, heroTileX, heroTileY, false); m.stuckT = 0; }
        } else if (d > 12) {
          moveActor(m, ((tgtX - m.x) / d) * 120 * dt, ((tgtY - m.y) / d) * 120 * dt);
          if (m.stuckT > 0.8 || Math.hypot(hero.x - m.x, hero.y - m.y) > 160) {
            setPathTo(m, heroTileX, heroTileY, false);
            m.stuckT = 0;
          }
        }
        // spot a workable deposit
        if (!danger) {
          for (const dp of deposits) {
            if (!dp.discovered || dp.amount <= 0) continue;
            const dpx = (dp.tx + 0.5) * TILE, dpy = (dp.ty + 0.5) * TILE;
            if (Math.hypot(dpx - m.x, dpy - m.y) < 76) {
              m.state = 'mine'; m.deposit = dp; m.path = null;
              addFloater(m.x, m.y - 12, 'mining!', '#80d0ff');
              break;
            }
          }
        }
      }
    } else if (m.state === 'mine') {
      const dp = m.deposit;
      if (!dp || dp.amount <= 0) { startReturn(m); }
      else if (danger) {
        m.state = 'flee';
        setPathTo(m, hall.tx, hall.ty, false);
        addFloater(m.x, m.y - 12, 'monsters!', '#ff6060');
      } else {
        const take = Math.min(MINER_GATHER * dt, dp.amount, MINER_CARRY - m.carry);
        dp.amount -= take;
        m.carry += take;
        if (Math.random() < dt * 2) addEffect((dp.tx + 0.5) * TILE, (dp.ty + 0.5) * TILE, 'hit');
        if (dp.amount <= 0) {
          terrain[idx(dp.tx, dp.ty)] = T_GRASS;
          announce('a gold deposit is exhausted', '#c8b890');
        }
        if (m.carry >= MINER_CARRY || dp.amount <= 0) startReturn(m);
      }
    } else if (m.state === 'return' || m.state === 'flee') {
      const speed = m.state === 'flee' ? 150 : 110;
      followPath(m, speed, dt);
      if (m.stuckT > 1) { setPathTo(m, hall.tx, hall.ty, false); m.stuckT = 0; }
      if (!m.path || m.pathIdx >= m.path.length || Math.hypot(hx - m.x, hy - m.y) < 90) {
        if (m.carry > 0) {
          const got = Math.round(m.carry);
          gold += got;
          m.carry = 0;
          addFloater(m.x, m.y - 12, `+${got}g delivered`, '#e8c83a');
        }
        if (m.state === 'return' && m.deposit && m.deposit.amount > 0) {
          m.state = 'commute';
          setPathTo(m, m.deposit.tx, m.deposit.ty, false);
        } else {
          m.state = 'idle';
          m.deposit = null;
          m.path = null;
        }
      }
    } else if (m.state === 'commute') {
      const dp = m.deposit;
      if (!dp || dp.amount <= 0) { m.state = 'idle'; m.path = null; }
      else if (danger && Math.hypot(danger.x - m.x, danger.y - m.y) < 140) {
        m.state = 'flee';
        setPathTo(m, hall.tx, hall.ty, false);
        addFloater(m.x, m.y - 12, 'monsters!', '#ff6060');
      } else {
        followPath(m, 110, dt);
        if (m.stuckT > 1) { setPathTo(m, dp.tx, dp.ty, false); m.stuckT = 0; }
        const dpx = (dp.tx + 0.5) * TILE, dpy = (dp.ty + 0.5) * TILE;
        if (Math.hypot(dpx - m.x, dpy - m.y) < 76) { m.state = 'mine'; m.path = null; }
        else if (!m.path || m.pathIdx >= m.path.length) setPathTo(m, dp.tx, dp.ty, false);
      }
    }

    if (m.hp <= 0) {
      addEffect(m.x, m.y, 'boom');
      announce('a miner was killed!', '#ff6060');
      miners.splice(i, 1);
    }
  }
}

function goHome(m) {
  m.state = 'flee';
  setPathTo(m, hall.tx, hall.ty, false);
}
function startReturn(m) {
  m.state = 'return';
  setPathTo(m, hall.tx, hall.ty, false);
}

function updateEnemies(dt) {
  for (const en of enemies) {
    en.atkCd -= dt;

    if (en.ai === 'wolf') {
      // pick a victim: hero or a miner, close to us and not too far from the den
      let victim = null, vd = 175;
      const candidates = (hero.dead || hero.arena) ? miners : [hero, ...miners];
      for (const c of candidates) {
        const d = Math.hypot(c.x - en.x, c.y - en.y);
        if (d < vd && Math.hypot(c.x - en.home.x, c.y - en.home.y) < 360) { victim = c; vd = d; }
      }
      if (victim) {
        const ang = Math.atan2(victim.y - en.y, victim.x - en.x);
        moveActor(en, Math.cos(ang) * 95 * dt, Math.sin(ang) * 95 * dt);
        if (en.atkCd <= 0 && vd < en.r + victim.r + 5) {
          en.atkCd = 0.9;
          victim.hp -= en.dmg;
          addEffect(victim.x, victim.y, 'hit');
          if (victim === hero && hero.hp <= 0) { hero.dead = true; hero.respawn = RESPAWN_TIME; }
        }
      } else {
        en.wt -= dt;
        if (en.wt <= 0) {
          en.wt = 2 + Math.random() * 2;
          en.wx = en.home.x + (Math.random() - 0.5) * 140;
          en.wy = en.home.y + (Math.random() - 0.5) * 140;
        }
        const d = Math.hypot(en.wx - en.x, en.wy - en.y);
        if (d > 6) moveActor(en, ((en.wx - en.x) / d) * 35 * dt, ((en.wy - en.y) / d) * 35 * dt);
      }
    } else {
      // raider: path to the hall, smash what blocks the way
      en.repathT -= dt;
      if (!en.path || en.repathT <= 0) {
        setPathTo(en, hall.tx, hall.ty, false);
        if (!en.path) setPathTo(en, hall.tx, hall.ty, true);   // fully walled in: smash through
        en.repathT = 3;
      }
      const blocked = followPath(en, en.speed, dt);
      const distHall = Math.hypot(hallCX() - en.x, hallCY() - en.y);
      let target = blocked;
      if (!target && distHall < TILE * 1.6) target = hall;
      if (target && en.atkCd <= 0) {
        en.atkCd = 0.8;
        target.hp -= en.dmg;
        addEffect((target.tx + 0.5) * TILE, (target.ty + 0.5) * TILE, 'hit');
        if (target.hp <= 0) destroyBuilding(target);
      }
      // swipe at the hero or miners on the way past
      if (en.atkCd <= 0) {
        const candidates = (hero.dead || hero.arena) ? miners : [hero, ...miners];
        for (const c of candidates) {
          if (Math.hypot(c.x - en.x, c.y - en.y) < en.r + c.r + 4) {
            en.atkCd = 0.8;
            c.hp -= en.dmg;
            addEffect(c.x, c.y, 'hit');
            if (c === hero && hero.hp <= 0) { hero.dead = true; hero.respawn = RESPAWN_TIME; }
            break;
          }
        }
      }
    }

    // separation
    for (const other of enemies) {
      if (other === en) continue;
      const d = Math.hypot(other.x - en.x, other.y - en.y);
      if (d > 0 && d < en.r + other.r) {
        en.x -= ((other.x - en.x) / d) * 14 * dt;
        en.y -= ((other.y - en.y) / d) * 14 * dt;
      }
    }
  }
  enemies = enemies.filter((e) => e.hp > 0);
}

function updateDens(dt) {
  for (let i = dens.length - 1; i >= 0; i--) {
    const den = dens[i];
    if (den.hp <= 0) {
      addFloater(den.x, den.y - 12, 'den destroyed!', '#80d0ff');
      addEffect(den.x, den.y, 'boom');
      announce('a wolf den was destroyed!', '#80d0ff');
      dens.splice(i, 1);
      continue;
    }
    den.spawnT -= dt;
    if (den.spawnT <= 0) {
      den.spawnT = 22;
      const pack = enemies.filter((e) => e.den === den).length;
      if (pack < 4) spawnWolf(den);
    }
  }
}

function updateBuildings(dt) {
  const seen = new Set();
  for (let i = 0; i < bgrid.length; i++) {
    const b = bgrid[i];
    if (!b || b === hall || seen.has(b)) continue;
    seen.add(b);
    const bx = (b.tx + 0.5) * TILE, by = (b.ty + 0.5) * TILE;

    if (b.kind === 'turret') {
      b.cd -= dt;
      let best = null, bd = TURRET_RANGE;
      for (const en of enemies) {
        const d = Math.hypot(en.x - bx, en.y - by);
        if (d < bd) { best = en; bd = d; }
      }
      if (best) {
        b.angle = Math.atan2(best.y - by, best.x - bx);
        if (b.cd <= 0) {
          b.cd = TURRET_CD;
          bullets.push({ x: bx + Math.cos(b.angle) * 12, y: by + Math.sin(b.angle) * 12,
            vx: Math.cos(b.angle) * 300, vy: Math.sin(b.angle) * 300,
            dmg: TURRET_DMG, life: 0.7, hero: false });
        }
      }
    } else if (b.kind === 'house') {
      b.incomeTimer += dt;
      if (b.incomeTimer >= HOUSE_TAX_EVERY) {
        b.incomeTimer -= HOUSE_TAX_EVERY;
        gold += 1;
      }
    }
  }
}

function updateBullets(dt) {
  for (const bl of bullets) {
    bl.x += bl.vx * dt;
    bl.y += bl.vy * dt;
    bl.life -= dt;
    if (bl.space) {                             // fired inside a portal arena
      if (bl.x < ARENA_PAD || bl.y < ARENA_PAD
        || bl.x > ARENA_W - ARENA_PAD || bl.y > ARENA_H - ARENA_PAD) { bl.life = 0; continue; }
      for (const m of bl.space.mobs) {
        if (m.hp <= 0) continue;
        if (Math.hypot(m.x - bl.x, m.y - bl.y) < m.r + 3) {
          damageEnemy(m, bl.dmg, bl.space);
          bl.life = 0;
          break;
        }
      }
      continue;
    }
    const tx = Math.floor(bl.x / TILE), ty = Math.floor(bl.y / TILE);
    if (!inWorld(tx, ty)) { bl.life = 0; continue; }
    const t = terrain[idx(tx, ty)];
    if (t === T_MOUNTAIN || t === T_DEPOSIT) { bl.life = 0; continue; }
    let hit = false;
    for (const en of enemies) {
      if (en.hp <= 0) continue;
      if (Math.hypot(en.x - bl.x, en.y - bl.y) < en.r + 3) {
        damageEnemy(en, bl.dmg);
        bl.life = 0; hit = true;
        break;
      }
    }
    if (!hit && bl.hero) {
      for (const den of dens) {
        if (Math.hypot(den.x - bl.x, den.y - bl.y) < 18) {
          damageDen(den, bl.dmg);
          bl.life = 0;
          break;
        }
      }
    }
  }
  bullets = bullets.filter((b) => b.life > 0);
}

function damageEnemy(en, dmg, space = null) {
  en.hp -= dmg;
  addEffect(en.x, en.y, 'hit', 0, space);
  if (en.hp <= 0) addEffect(en.x, en.y, 'boom', 0, space);
}
function damageDen(den, dmg) {
  den.hp -= dmg;
  addEffect(den.x, den.y, 'hit');
}

function addEffect(x, y, type, angle = 0, space = null) {
  effects.push({ x, y, type, angle, space, life: type === 'slash' ? 0.15 : 0.2 });
}
function addFloater(x, y, text, color) {
  floaters.push({ x, y, text, color, life: 1.4 });
}
function announce(text, color) {
  announcements.unshift({ text, color, life: 5 });
  if (announcements.length > 4) announcements.pop();
}

// ---------------------------------------------------------------- render
function tileShade(tx, ty) {
  let h = (tx * 73856093) ^ (ty * 19349663);
  h = (h ^ (h >> 13)) & 0xffff;
  return h / 0xffff;
}

function drawViewport(cam, vx, vw, isBuilder) {
  ctx.save();
  ctx.beginPath();
  ctx.rect(vx, HUD_H, vw, VIEW_H);
  ctx.clip();
  ctx.translate(vx - cam.x, HUD_H - cam.y);

  const t0x = Math.max(0, Math.floor(cam.x / TILE));
  const t1x = Math.min(WT - 1, Math.ceil((cam.x + vw) / TILE));
  const t0y = Math.max(0, Math.floor(cam.y / TILE));
  const t1y = Math.min(HT - 1, Math.ceil((cam.y + VIEW_H) / TILE));

  // terrain
  for (let ty = t0y; ty <= t1y; ty++) {
    for (let tx = t0x; tx <= t1x; tx++) {
      if (!revealed[idx(tx, ty)]) continue;
      const px = tx * TILE, py = ty * TILE;
      const v = tileShade(tx, ty);
      ctx.fillStyle = v < 0.5 ? '#27392a' : v < 0.8 ? '#2b3f2d' : '#243527';
      ctx.fillRect(px, py, TILE, TILE);
      const t = terrain[idx(tx, ty)];
      if (t === T_FOREST) ctx.drawImage(SPR.tree, px, py, TILE, TILE);
      else if (t === T_MOUNTAIN) ctx.drawImage(SPR.rock, px, py, TILE, TILE);
      else if (t === T_DEPOSIT) ctx.drawImage(SPR.deposit, px, py, TILE, TILE);
      else if (v > 0.93) {
        ctx.fillStyle = '#33502f';
        ctx.fillRect(px + 8, py + 12, 4, 4);
        ctx.fillRect(px + 20, py + 20, 4, 4);
      }
    }
  }

  // build radius hint (builder side only)
  if (isBuilder && state === 'play') {
    ctx.strokeStyle = 'rgba(200,184,144,0.15)';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(hallCX(), hallCY(), BUILD_RADIUS * TILE, 0, Math.PI * 2);
    ctx.stroke();
  }

  // portals
  for (const p of portals) {
    if (!revealed[idx(Math.floor(p.x / TILE), Math.floor(p.y / TILE))]) continue;
    drawPortal(p);
  }

  // dens
  for (const den of dens) {
    if (!revealed[idx(Math.floor(den.x / TILE), Math.floor(den.y / TILE))]) continue;
    ctx.drawImage(SPR.den, den.x - 20, den.y - 20, 40, 40);
    if (den.hp < den.maxHp) drawBar(den.x - 14, den.y - 26, 28, den.hp / den.maxHp, '#e05050');
  }

  // buildings
  const seen = new Set();
  for (let ty = t0y; ty <= t1y; ty++) {
    for (let tx = t0x; tx <= t1x; tx++) {
      const b = bgrid[idx(tx, ty)];
      if (!b || seen.has(b)) continue;
      seen.add(b);
      const px = b.tx * TILE, py = b.ty * TILE;
      if (b.kind === 'hall') ctx.drawImage(SPR.hall, px, py, TILE * 2, TILE * 2);
      else if (b.kind === 'wall') ctx.drawImage(SPR.wall, px, py, TILE, TILE);
      else if (b.kind === 'house') ctx.drawImage(SPR.house, px, py, TILE, TILE);
      else if (b.kind === 'turret') {
        ctx.drawImage(SPR.turretBase, px, py, TILE, TILE);
        ctx.save();
        ctx.translate(px + TILE / 2, py + TILE / 2);
        ctx.rotate(b.angle);
        ctx.fillStyle = '#2f2f3a';
        ctx.fillRect(0, -3, 16, 6);
        ctx.fillStyle = '#55555f';
        ctx.fillRect(12, -4, 5, 8);
        ctx.restore();
      }
      if (b.hp < b.maxHp) {
        const w = b.kind === 'hall' ? TILE * 2 : TILE;
        drawBar(px + 2, py - 6, w - 4, b.hp / b.maxHp, '#e05050');
      }
    }
  }

  // miners
  for (const m of miners) {
    ctx.drawImage(SPR.miner, m.x - 13, m.y - 13, 26, 26);
    if (m.carry > 0) {
      ctx.fillStyle = '#e8c83a';
      ctx.fillRect(m.x - 3, m.y - 16, 6, 4);
    }
    if (m.hp < m.maxHp) drawBar(m.x - 10, m.y - 20, 20, m.hp / m.maxHp, '#50d060');
  }

  // enemies (only on revealed ground)
  for (const en of enemies) {
    if (!revealed[idx(Math.floor(en.x / TILE), Math.floor(en.y / TILE))]) continue;
    const spr = SPR[en.spr];
    const s = en.size || (en.spr === 'brute' ? 36 : 26);
    ctx.drawImage(spr, en.x - s / 2, en.y - s / 2, s, s);
    if (en.hp < en.maxHp) drawBar(en.x - 12, en.y - s / 2 - 6, 24, en.hp / en.maxHp, '#e05050');
  }

  // hero (not shown in the world while inside a portal arena)
  if (!hero.dead && !hero.arena) drawHero();

  // bullets
  for (const bl of bullets) {
    if (bl.space) continue;
    ctx.fillStyle = bl.hero ? '#ffe080' : '#80d0ff';
    ctx.fillRect(bl.x - 2, bl.y - 2, 4, 4);
  }

  // effects
  for (const fx of effects) {
    if (fx.space) continue;
    if (fx.type === 'hit') {
      ctx.fillStyle = `rgba(255,255,255,${fx.life * 4})`;
      ctx.fillRect(fx.x - 4, fx.y - 4, 8, 8);
    } else if (fx.type === 'boom') {
      ctx.fillStyle = `rgba(255,160,60,${fx.life * 4})`;
      ctx.beginPath();
      ctx.arc(fx.x, fx.y, (0.2 - fx.life) * 90 + 6, 0, Math.PI * 2);
      ctx.fill();
    } else if (fx.type === 'slash') {
      ctx.strokeStyle = `rgba(255,255,220,${fx.life * 6})`;
      ctx.lineWidth = 4;
      ctx.beginPath();
      ctx.arc(fx.x, fx.y, MELEE_RANGE - 6, fx.angle - Math.PI / 3, fx.angle + Math.PI / 3);
      ctx.stroke();
    }
  }

  // floaters
  ctx.font = 'bold 12px monospace';
  for (const fl of floaters) {
    ctx.globalAlpha = Math.min(1, fl.life);
    ctx.fillStyle = fl.color;
    ctx.fillText(fl.text, fl.x, fl.y);
    ctx.globalAlpha = 1;
  }

  // fog of war
  ctx.fillStyle = '#0a0812';
  for (let ty = t0y; ty <= t1y; ty++) {
    for (let tx = t0x; tx <= t1x; tx++) {
      if (!revealed[idx(tx, ty)]) ctx.fillRect(tx * TILE, ty * TILE, TILE + 1, TILE + 1);
    }
  }

  // builder cursor
  if (isBuilder && state === 'play') {
    const px = cursor.tx * TILE, py = cursor.ty * TILE;
    const existing = inWorld(cursor.tx, cursor.ty) ? bgrid[idx(cursor.tx, cursor.ty)] : null;
    let ok;
    if (cursor.tool === 'repair') ok = existing && existing.hp < existing.maxHp;
    else ok = canBuildAt(cursor.tx, cursor.ty) && canAfford(COSTS[cursor.tool]);
    ctx.strokeStyle = ok ? '#60ff80' : '#ff6060';
    ctx.lineWidth = 2;
    ctx.strokeRect(px + 1, py + 1, TILE - 2, TILE - 2);
    if (cursor.tool === 'turret' && ok) {
      ctx.strokeStyle = 'rgba(96,255,128,0.25)';
      ctx.beginPath();
      ctx.arc(px + TILE / 2, py + TILE / 2, TURRET_RANGE, 0, Math.PI * 2);
      ctx.stroke();
    }
  }

  ctx.restore();
}

function drawBar(x, y, w, ratio, color) {
  ctx.fillStyle = '#40202a';
  ctx.fillRect(x, y, w, 3);
  ctx.fillStyle = color;
  ctx.fillRect(x, y, w * Math.max(0, ratio), 3);
}

function drawHero() {
  ctx.drawImage(SPR.hero, hero.x - 14, hero.y - 14, 28, 28);
  if (hero.hasGun) {
    ctx.save();
    ctx.translate(hero.x, hero.y);
    ctx.rotate(hero.aim);
    ctx.fillStyle = '#22232e';
    ctx.fillRect(6, -2, 12, 4);
    ctx.restore();
  }
  drawBar(hero.x - 12, hero.y - 24, 24, hero.hp / HERO_MAX_HP, '#50d060');
  drawBar(hero.x - 12, hero.y - 20, 24, hero.stam / HERO_STAM_MAX, '#e8c83a');
}

function drawPortal(p) {
  const spin = time * 2.5;
  ctx.fillStyle = 'rgba(64,224,128,0.18)';
  ctx.beginPath();
  ctx.arc(p.x, p.y, 16, 0, Math.PI * 2);
  ctx.fill();
  ctx.lineWidth = 3;
  for (let i = 0; i < 3; i++) {
    ctx.strokeStyle = i === 0 ? '#40e080' : 'rgba(64,224,128,0.55)';
    ctx.beginPath();
    ctx.arc(p.x, p.y, 8 + i * 5, spin + i * 2.1, spin + i * 2.1 + Math.PI * 1.2);
    ctx.stroke();
  }
  drawBar(p.x - 14, p.y - 28, 28, p.t / PORTAL_BREAK_TIME, '#40e080');
}

// the pocket dimension behind a portal — drawn instead of the hero's world viewport
function drawArena() {
  const p = hero.arena;
  ctx.save();
  ctx.beginPath();
  ctx.rect(RIGHT_VX, HUD_H, RIGHT_VW, VIEW_H);
  ctx.clip();
  ctx.fillStyle = '#060a08';
  ctx.fillRect(RIGHT_VX, HUD_H, RIGHT_VW, VIEW_H);
  ctx.translate(RIGHT_VX - heroCam.x, HUD_H - heroCam.y);

  for (let ty = 0; ty < ARENA_HT; ty++) {
    for (let tx = 0; tx < ARENA_WT; tx++) {
      const px = tx * TILE, py = ty * TILE;
      const edge = tx === 0 || ty === 0 || tx === ARENA_WT - 1 || ty === ARENA_HT - 1;
      ctx.fillStyle = (tx + ty) % 2 ? '#152318' : '#182a1b';
      ctx.fillRect(px, py, TILE, TILE);
      if (edge) ctx.drawImage(SPR.rock, px, py, TILE, TILE);
    }
  }

  for (const m of p.mobs) {
    const s = m.size;
    if (m.isBoss) {
      ctx.fillStyle = 'rgba(64,224,128,0.16)';
      ctx.beginPath();
      ctx.arc(m.x, m.y, s / 2 + 8, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.drawImage(SPR.wolf, m.x - s / 2, m.y - s / 2, s, s);
    if (!m.isBoss && m.hp < m.maxHp) drawBar(m.x - 12, m.y - s / 2 - 6, 24, m.hp / m.maxHp, '#e05050');
  }

  if (!hero.dead) drawHero();

  for (const bl of bullets) {
    if (bl.space !== p) continue;
    ctx.fillStyle = '#ffe080';
    ctx.fillRect(bl.x - 2, bl.y - 2, 4, 4);
  }
  for (const fx of effects) {
    if (fx.space !== p) continue;
    if (fx.type === 'hit') {
      ctx.fillStyle = `rgba(255,255,255,${fx.life * 4})`;
      ctx.fillRect(fx.x - 4, fx.y - 4, 8, 8);
    } else if (fx.type === 'boom') {
      ctx.fillStyle = `rgba(255,160,60,${fx.life * 4})`;
      ctx.beginPath();
      ctx.arc(fx.x, fx.y, (0.2 - fx.life) * 90 + 6, 0, Math.PI * 2);
      ctx.fill();
    } else if (fx.type === 'slash') {
      ctx.strokeStyle = `rgba(255,255,220,${fx.life * 6})`;
      ctx.lineWidth = 4;
      ctx.beginPath();
      ctx.arc(fx.x, fx.y, MELEE_RANGE - 6, fx.angle - Math.PI / 3, fx.angle + Math.PI / 3);
      ctx.stroke();
    }
  }
  ctx.restore();

  // arena overlay: title + boss bar
  ctx.textAlign = 'center';
  ctx.font = 'bold 16px monospace';
  ctx.fillStyle = '#40e080';
  ctx.fillText('GREEN PORTAL — slay the ALPHA WOLF!', RIGHT_VX + RIGHT_VW / 2, HUD_H + 26);
  const boss = p.mobs.find((m) => m.isBoss);
  if (boss) {
    const bw = 300, bx = RIGHT_VX + RIGHT_VW / 2 - bw / 2, by = HUD_H + 36;
    ctx.fillStyle = '#40202a';
    ctx.fillRect(bx, by, bw, 10);
    ctx.fillStyle = '#e05050';
    ctx.fillRect(bx, by, bw * Math.max(0, boss.hp / boss.maxHp), 10);
  }
  ctx.textAlign = 'left';
}

// ---------------------------------------------------------------- minimap
function renderMinimapBase() {
  const g = minimap.getContext('2d');
  const img = g.createImageData(WT, HT);
  const put = (i, r, gg, b) => { img.data[i * 4] = r; img.data[i * 4 + 1] = gg; img.data[i * 4 + 2] = b; img.data[i * 4 + 3] = 255; };
  for (let i = 0; i < WT * HT; i++) {
    if (!revealed[i]) { put(i, 8, 6, 14); continue; }
    const t = terrain[i];
    if (t === T_MOUNTAIN) put(i, 106, 106, 116);
    else if (t === T_FOREST) put(i, 30, 74, 34);
    else if (t === T_DEPOSIT) put(i, 232, 200, 58);
    else put(i, 39, 57, 42);
    const b = bgrid[i];
    if (b) b.kind === 'hall' ? put(i, 224, 48, 48) : put(i, 200, 184, 144);
  }
  g.putImageData(img, 0, 0);
}

function drawMinimap() {
  const scale = 2;
  const mw = WT * scale, mh = HT * scale;
  const mx = 10, my = H - mh - 10;
  ctx.globalAlpha = 0.92;
  ctx.fillStyle = '#0a0812';
  ctx.fillRect(mx - 2, my - 2, mw + 4, mh + 4);
  ctx.drawImage(minimap, mx, my, mw, mh);
  ctx.globalAlpha = 1;

  const dot = (x, y, color, s = 3) => {
    ctx.fillStyle = color;
    ctx.fillRect(mx + (x / TILE) * scale - s / 2, my + (y / TILE) * scale - s / 2, s, s);
  };
  for (const m of miners) dot(m.x, m.y, '#80d0ff', 2);
  for (const en of enemies) if (en.ai === 'raider') dot(en.x, en.y, '#ff4040', 3);
  for (const p of portals) if (time % 0.8 < 0.5) dot(p.x, p.y, '#40e080', 4);
  if (!hero.dead && !hero.arena) dot(hero.x, hero.y, '#ffffff', 3);
  // viewport boxes
  ctx.strokeStyle = 'rgba(255,255,255,0.35)';
  ctx.lineWidth = 1;
  ctx.strokeRect(mx + (builderCam.x / TILE) * scale, my + (builderCam.y / TILE) * scale,
    (LEFT_VW / TILE) * scale, (VIEW_H / TILE) * scale);
}

// ---------------------------------------------------------------- HUD
function drawHUD() {
  ctx.fillStyle = '#100c18';
  ctx.fillRect(0, 0, W, HUD_H);
  ctx.fillStyle = '#2a2438';
  ctx.fillRect(LEFT_VW, HUD_H, RIGHT_VX - LEFT_VW, VIEW_H);

  ctx.font = 'bold 15px monospace';
  ctx.fillStyle = '#e8c83a';
  ctx.fillText(`gold ${Math.floor(gold)}`, 12, 23);
  ctx.fillStyle = '#c8905a';
  ctx.fillText(`wood ${Math.floor(wood)}`, 100, 23);
  ctx.fillStyle = '#a0a0b0';
  ctx.fillText(`stone ${Math.floor(stone)}`, 190, 23);
  ctx.fillStyle = '#e07070';
  ctx.fillText(`meat ${Math.floor(meat)}`, 290, 23);

  ctx.fillStyle = '#80d0ff';
  ctx.fillText(`miners ${miners.length}/${minerCap()}`, 12, 45);
  const raiders = enemies.filter((e) => e.ai === 'raider').length;
  if (raiders > 0) {
    ctx.fillStyle = '#ff6060';
    ctx.fillText(`LOOSE! ${raiders}`, 130, 45);
  } else if (portals.length > 0) {
    ctx.fillStyle = '#40e080';
    ctx.fillText(`breaks in ${Math.ceil(Math.min(...portals.map((p) => p.t)))}s`, 130, 45);
  } else {
    ctx.fillStyle = '#e8e0d0';
    ctx.fillText(`portal in ${Math.ceil(portalT)}s`, 130, 45);
  }
  ctx.fillStyle = '#e8e0d0';
  ctx.fillText(`mines ${deposits.filter((d) => d.discovered).length}/${deposits.length}`, 280, 45);

  ctx.fillStyle = '#e8e0d0';
  ctx.fillText('hall', 400, 23);
  ctx.fillStyle = '#40202a'; ctx.fillRect(440, 12, 130, 12);
  ctx.fillStyle = '#e05050'; ctx.fillRect(440, 12, 130 * Math.max(0, hall.hp / hall.maxHp), 12);
  ctx.fillStyle = '#e8e0d0';
  ctx.fillText('hero', 400, 45);
  ctx.fillStyle = '#40202a'; ctx.fillRect(440, 34, 130, 8);
  ctx.fillStyle = '#50d060'; ctx.fillRect(440, 34, 130 * Math.max(0, hero.hp / HERO_MAX_HP), 8);
  ctx.fillStyle = '#40202a'; ctx.fillRect(440, 44, 130, 5);
  ctx.fillStyle = '#e8c83a'; ctx.fillRect(440, 44, 130 * Math.max(0, hero.stam / HERO_STAM_MAX), 5);

  const tools = [
    ['Y', 'wall', costText(COSTS.wall)], ['U', 'turret', costText(COSTS.turret)],
    ['I', 'house', costText(COSTS.house)], ['O', 'repair', 'gold'],
    ['P', 'hire', `${MINER_COST}g`],
  ];
  let x = 620;
  for (const [key, name, cost] of tools) {
    const sel = cursor.tool === name;
    ctx.fillStyle = sel ? '#3a3454' : '#1c1828';
    ctx.fillRect(x, 6, 92, 44);
    if (sel) { ctx.strokeStyle = '#8a80c0'; ctx.strokeRect(x + 0.5, 6.5, 91, 43); }
    ctx.fillStyle = sel ? '#fff' : '#a8a0b8';
    ctx.font = 'bold 13px monospace';
    ctx.fillText(`${key} ${name}`, x + 7, 24);
    ctx.fillStyle = '#e8c83a';
    ctx.fillText(cost, x + 7, 43);
    x += 98;
  }

  ctx.fillStyle = '#6a6480';
  ctx.font = '12px monospace';
  ctx.fillText('BUILDER', LEFT_VX + 8, HUD_H + 16);
  ctx.fillText('HERO', RIGHT_VX + 8, HUD_H + 16);
  if (!hero.hasGun) {
    ctx.fillStyle = '#e8c83a';
    ctx.fillText(`bare-handed — buy pistol at hall: E (${PISTOL_COST}g)`, RIGHT_VX + 56, HUD_H + 16);
  }

  // announcements
  ctx.font = 'bold 14px monospace';
  ctx.textAlign = 'center';
  announcements.forEach((an, i) => {
    ctx.globalAlpha = Math.min(1, an.life);
    ctx.fillStyle = '#0a0812';
    const tw = ctx.measureText(an.text).width;
    ctx.fillRect(W / 2 - tw / 2 - 8, HUD_H + 8 + i * 24, tw + 16, 20);
    ctx.fillStyle = an.color;
    ctx.fillText(an.text, W / 2, HUD_H + 22 + i * 24);
    ctx.globalAlpha = 1;
  });
  ctx.textAlign = 'left';
}

function drawTitle() {
  ctx.fillStyle = 'rgba(10,8,16,0.9)';
  ctx.fillRect(0, 0, W, H);
  ctx.textAlign = 'center';
  ctx.fillStyle = '#e8c83a';
  ctx.font = 'bold 44px monospace';
  ctx.fillText('HALL DEFENDERS', W / 2, 130);
  ctx.fillStyle = '#a8a0b8';
  ctx.font = '18px monospace';
  ctx.fillText('— a kingdom co-op game —', W / 2, 165);
  ctx.fillStyle = '#e8e0d0';
  ctx.font = '16px monospace';
  const lines = [
    'the world is dark. the HERO (right screen) explores it and finds gold deposits.',
    'the BUILDER (left screen) hires miners — escort them and they will mine gold.',
    'gold ONLY comes from the mines. wood, stone and meat trickle in over time.',
    'GREEN PORTALS open in the wild — walk in (E) and slay the ALPHA WOLF inside,',
    'or the timer runs out, the portal breaks, and its monsters charge the hall!',
    '',
    'BUILDER — arrows: cursor (shift = fast)   Y/U/I/O: tool   enter: build/repair',
    `delete: sell   P: hire miner (${MINER_COST}g)   wall ${costText(COSTS.wall)}   turret ${costText(COSTS.turret)}   house ${costText(COSTS.house)}`,
    '',
    'HERO — WASD: move   shift: dash (stamina)   mouse: aim   space: punch   E: portal/shop',
    `wolves are faster than you — dash away! pistol at the hall: E (${PISTOL_COST}g)`,
    `stand near the hall to heal. reviving the hero costs ${REVIVE_MEAT_COST} meat!`,
    '',
    'press ENTER or click to start',
  ];
  lines.forEach((l, i) => ctx.fillText(l, W / 2, 220 + i * 28));
  ctx.textAlign = 'left';
}

function drawGameOver() {
  ctx.fillStyle = 'rgba(10,8,16,0.85)';
  ctx.fillRect(0, 0, W, H);
  ctx.textAlign = 'center';
  ctx.fillStyle = '#e05050';
  ctx.font = 'bold 44px monospace';
  ctx.fillText('THE HALL HAS FALLEN', W / 2, H / 2 - 40);
  ctx.fillStyle = '#e8e0d0';
  ctx.font = '20px monospace';
  ctx.fillText(`you faced ${portalLevel} portal${portalLevel === 1 ? '' : 's'} and banked ${Math.floor(gold)} gold`, W / 2, H / 2 + 10);
  ctx.fillText('press R to try again', W / 2, H / 2 + 48);
  ctx.textAlign = 'left';
}

function draw() {
  ctx.fillStyle = '#0a0812';
  ctx.fillRect(0, 0, W, H);
  drawViewport(builderCam, LEFT_VX, LEFT_VW, true);
  if (hero.arena) drawArena();
  else drawViewport(heroCam, RIGHT_VX, RIGHT_VW, false);
  drawHUD();
  drawMinimap();

  if (hero.dead && state === 'play') {
    ctx.fillStyle = '#ffd0d0';
    ctx.font = 'bold 16px monospace';
    ctx.textAlign = 'center';
    const msg = hero.respawn > 0
      ? `hero down! respawn in ${Math.ceil(hero.respawn)}...`
      : `hero down! needs ${REVIVE_MEAT_COST} meat to revive (${Math.floor(meat)}/${REVIVE_MEAT_COST})`;
    ctx.fillText(msg, RIGHT_VX + RIGHT_VW / 2, HUD_H + 40);
    ctx.textAlign = 'left';
  }
  if (state === 'title') drawTitle();
  if (state === 'over') drawGameOver();
}

// ---------------------------------------------------------------- main loop
let last = performance.now();
function frame(now) {
  const dt = Math.min((now - last) / 1000, 0.05);
  last = now;
  if (state === 'play') update(dt);
  draw();
  requestAnimationFrame(frame);
}

newGame();
requestAnimationFrame(frame);
})();
