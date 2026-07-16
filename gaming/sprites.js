// Pixel-art sprites drawn in code — no asset files needed.
(() => {
'use strict';

function makeSprite(rows, palette) {
  const h = rows.length, w = rows[0].length;
  const c = document.createElement('canvas');
  c.width = w; c.height = h;
  const g = c.getContext('2d');
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const ch = rows[y][x];
      if (ch === '.' || ch === ' ' || !palette[ch]) continue;
      g.fillStyle = palette[ch];
      g.fillRect(x, y, 1, 1);
    }
  }
  return c;
}

const SPR = {};

const HUMAN_ROWS = [
  '................',
  '.....hhhhhh.....',
  '.....hhhhhh.....',
  '.....ffffff.....',
  '.....feffef.....',
  '.....ffffff.....',
  '......ffff......',
  '....bbbbbbbb....',
  '...fbbbbbbbbf...',
  '...fbbbbbbbbf...',
  '....bbbbbbbb....',
  '......b..b......',
  '.....bb..bb.....',
  '.....bb..bb.....',
  '.....ss..ss.....',
  '................',
];

SPR.hero = makeSprite(HUMAN_ROWS,
  { h: '#5a3b1e', f: '#e8b88a', e: '#22232e', b: '#b03030', s: '#33333e' });

// miner: yellow helmet, brown work clothes
SPR.miner = makeSprite(HUMAN_ROWS,
  { h: '#e8c83a', f: '#e8b88a', e: '#22232e', b: '#7a5a3a', s: '#33333e' });

// lumberjack: green cap, tan work clothes
SPR.lumber = makeSprite(HUMAN_ROWS,
  { h: '#3a7534', f: '#e8b88a', e: '#22232e', b: '#8a6a3a', s: '#33333e' });

// archer: green hood and tunic
SPR.archer = makeSprite(HUMAN_ROWS,
  { h: '#2f6f3a', f: '#e8b88a', e: '#22232e', b: '#4a8a52', s: '#33333e' });

// knight: steel helmet and armor
SPR.knight = makeSprite(HUMAN_ROWS,
  { h: '#8a8a96', f: '#e8b88a', e: '#22232e', b: '#6a6a78', s: '#33333e' });

SPR.grunt = makeSprite([
  '................',
  '....gggggggg....',
  '...gggggggggg...',
  '...ggrggggrgg...',
  '...gggggggggg...',
  '....gggggggg....',
  '.....dddddd.....',
  '....dddddddd....',
  '...g.dddddd.g...',
  '...g.dddddd.g...',
  '.....dddddd.....',
  '.....dd..dd.....',
  '....ggg..ggg....',
  '................',
  '................',
  '................',
], { g: '#4f8f3a', r: '#e03030', d: '#3a5f2a' });

SPR.brute = makeSprite([
  '...pppppppppp...',
  '..pppppppppppp..',
  '..pprpppppprpp..',
  '..pppppppppppp..',
  '..pppppppppppp..',
  '...pppppppppp...',
  '..dddddddddddd..',
  '.dddddddddddddd.',
  '.pp.dddddddd.pp.',
  '.pp.dddddddd.pp.',
  '....dddddddd....',
  '....ddd..ddd....',
  '...ppp....ppp...',
  '...ppp....ppp...',
  '..pppp....pppp..',
  '................',
], { p: '#9a4a3a', d: '#4a3a5a', r: '#ffd23a' });

SPR.wolf = makeSprite([
  '................',
  '................',
  '...ww...........',
  '..wwww..........',
  '..wrww..........',
  '..wwwwwwwwwww...',
  '...wwwwwwwwwww..',
  '...wwwwwwwwwwd..',
  '....wwwwwwwww...',
  '....ww.....ww...',
  '....ww.....ww...',
  '...dww....dww...',
  '................',
  '................',
  '................',
  '................',
], { w: '#9a9aa6', r: '#e03030', d: '#5a5a66' });

// brick wall, generated
SPR.wall = (() => {
  const rows = [];
  for (let y = 0; y < 16; y++) {
    let row = '';
    const mortarRow = y % 4 === 3;
    const off = (Math.floor(y / 4) % 2) * 4;
    for (let x = 0; x < 16; x++) {
      row += (mortarRow || (x + off) % 8 === 0) ? 'm' : 'b';
    }
    rows.push(row);
  }
  return makeSprite(rows, { b: '#8a8a96', m: '#55555f' });
})();

// mountain rock tile, generated speckle
SPR.rock = (() => {
  const rows = [];
  for (let y = 0; y < 16; y++) {
    let row = '';
    for (let x = 0; x < 16; x++) {
      const h = (x * 7 + y * 13 + x * y) % 11;
      row += h < 2 ? 'd' : h < 4 ? 'l' : 's';
    }
    rows.push(row);
  }
  return makeSprite(rows, { s: '#6a6a74', l: '#82828e', d: '#4e4e58' });
})();

SPR.turretBase = makeSprite([
  '................',
  '................',
  '....ssssssss....',
  '...ssssssssss...',
  '..ssmmmmmmmmss..',
  '..ssmmmmmmmmss..',
  '..ssmmmccmmmss..',
  '..ssmmccccmmss..',
  '..ssmmccccmmss..',
  '..ssmmmccmmmss..',
  '..ssmmmmmmmmss..',
  '..ssmmmmmmmmss..',
  '...ssssssssss...',
  '....ssssssss....',
  '................',
  '................',
], { s: '#55555f', m: '#8a8a96', c: '#2f2f3a' });

SPR.house = makeSprite([
  '................',
  '......rrrr......',
  '....rrrrrrrr....',
  '..rrrrrrrrrrrr..',
  '.rrrrrrrrrrrrrr.',
  '..wwwwwwwwwwww..',
  '..wwwwwwwwwwww..',
  '..wwdwwwwwwdww..',
  '..wwdwwwwwwdww..',
  '..wwwwwwwwwwww..',
  '..wwwwwddwwwww..',
  '..wwwwwddwwwww..',
  '..wwwwwddwwwww..',
  '................',
  '................',
  '................',
], { r: '#a04a30', w: '#c8b890', d: '#3a2f28' });

SPR.hall = makeSprite([
  '.......f........',
  '.......ff.......',
  '.......f........',
  '.......w........',
  '..w..wwwww..w...',
  '.www.wwwww.www..',
  '.www.wwwww.www..',
  '.wwwwwwwwwwwww..',
  '.wwwwwwwwwwwww..',
  '.wwdwwwwwwwdww..',
  '.wwwwwwwwwwwww..',
  '.wwwwwdddwwwww..',
  '.wwwwwdddwwwww..',
  '.wwwwwdddwwwww..',
  '.wwwwwwwwwwwww..',
  '................',
], { f: '#e03030', w: '#b0a890', d: '#3a2f28' });

SPR.tree = makeSprite([
  '................',
  '......gggg......',
  '....gglggggg....',
  '...gggggggggg...',
  '...ggggglgggg...',
  '....gglggggg....',
  '.....gggggg.....',
  '......gggg......',
  '.......tt.......',
  '.......tt.......',
  '.......tt.......',
  '......ttt.......',
  '................',
  '................',
  '................',
  '................',
], { g: '#2f5f2a', l: '#3a7534', t: '#5a3b1e' });

SPR.deposit = makeSprite([
  '................',
  '....ssssss......',
  '...ssssssss.....',
  '..ssgssssgss....',
  '..ssssggssss....',
  '.sssgssssgsss...',
  '.ssssssggssss...',
  '.sssgssssssss...',
  '..sssssgssss....',
  '...ssssssss.....',
  '....gsssss......',
  '................',
  '................',
  '................',
  '................',
  '................',
], { s: '#6a6a74', g: '#e8c83a' });

SPR.den = makeSprite([
  '................',
  '.....dddddd.....',
  '....dddddddd....',
  '...dddddddddd...',
  '..ddbbbbbbbbdd..',
  '..ddbbbbbbbbdd..',
  '..ddbbbbbbbbdd..',
  '.ddddbbbbbbdddd.',
  '.dddddddddddddd.',
  '..w..w....w.w...',
  '................',
  '................',
  '................',
  '................',
  '................',
  '................',
], { d: '#5a4a44', b: '#16100e', w: '#d8d0c0' });

window.SPR = SPR;
})();
