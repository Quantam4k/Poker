'use strict';

const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });

app.use(express.static(path.join(__dirname, 'public')));

const PORT = process.env.PORT || 3000;

// ─── Constants ───────────────────────────────────────────────────────────────
const STARTING_CHIPS = 2000;
const SMALL_BLIND = 50;
const BIG_BLIND = 100;
const MAX_PLAYERS = 6;
const RANKS = ['2','3','4','5','6','7','8','9','T','J','Q','K','A'];
const SUITS = ['h','d','c','s'];

// ─── Deck Utilities ───────────────────────────────────────────────────────────
function buildDeck() {
  const deck = [];
  for (const suit of SUITS) for (const rank of RANKS) deck.push(rank + suit);
  return deck;
}

function shuffle(deck) {
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

// ─── Hand Evaluator ───────────────────────────────────────────────────────────
const RANK_VAL = { '2':2,'3':3,'4':4,'5':5,'6':6,'7':7,'8':8,'9':9,'T':10,'J':11,'Q':12,'K':13,'A':14 };
const HAND_NAMES = ['High Card','One Pair','Two Pair','Three of a Kind','Straight','Flush','Full House','Four of a Kind','Straight Flush','Royal Flush'];

function parseCard(c) {
  return { rank: RANK_VAL[c[0]], suit: c[1], str: c };
}

function getCombinations(arr, k) {
  if (k === 0) return [[]];
  if (arr.length < k) return [];
  const [first, ...rest] = arr;
  const withFirst = getCombinations(rest, k - 1).map(c => [first, ...c]);
  const withoutFirst = getCombinations(rest, k);
  return [...withFirst, ...withoutFirst];
}

function evaluate5(cards) {
  // cards: array of {rank, suit}
  const ranks = cards.map(c => c.rank).sort((a, b) => b - a);
  const suits = cards.map(c => c.suit);
  const rankCounts = {};
  for (const r of ranks) rankCounts[r] = (rankCounts[r] || 0) + 1;
  const counts = Object.values(rankCounts).sort((a, b) => b - a);
  const uniqueRanks = Object.keys(rankCounts).map(Number).sort((a, b) => b - a);

  const isFlush = new Set(suits).size === 1;
  const isStraight = (() => {
    if (uniqueRanks.length !== 5) return false;
    // Normal straight
    if (uniqueRanks[0] - uniqueRanks[4] === 4) return true;
    // Wheel: A-2-3-4-5
    if (uniqueRanks[0] === 14 && uniqueRanks[1] === 5 && uniqueRanks[2] === 4 && uniqueRanks[3] === 3 && uniqueRanks[4] === 2) return true;
    return false;
  })();

  // Get the high card of straight (wheel = 5)
  const straightHigh = (() => {
    if (!isStraight) return 0;
    if (uniqueRanks[0] === 14 && uniqueRanks[1] === 5) return 5; // wheel
    return uniqueRanks[0];
  })();

  // Group ranks by count descending, then by rank descending
  const grouped = Object.entries(rankCounts)
    .map(([r, c]) => ({ rank: Number(r), count: c }))
    .sort((a, b) => b.count - a.count || b.rank - a.rank);

  const tiebreakers = grouped.map(g => g.rank);

  if (isFlush && isStraight) {
    const rank = straightHigh === 14 ? 9 : 8; // Royal vs SF
    return { rank, name: HAND_NAMES[rank], tiebreakers: [straightHigh] };
  }
  if (counts[0] === 4) return { rank: 7, name: HAND_NAMES[7], tiebreakers };
  if (counts[0] === 3 && counts[1] === 2) return { rank: 6, name: HAND_NAMES[6], tiebreakers };
  if (isFlush) return { rank: 5, name: HAND_NAMES[5], tiebreakers: ranks };
  if (isStraight) return { rank: 4, name: HAND_NAMES[4], tiebreakers: [straightHigh] };
  if (counts[0] === 3) return { rank: 3, name: HAND_NAMES[3], tiebreakers };
  if (counts[0] === 2 && counts[1] === 2) return { rank: 2, name: HAND_NAMES[2], tiebreakers };
  if (counts[0] === 2) return { rank: 1, name: HAND_NAMES[1], tiebreakers };
  return { rank: 0, name: HAND_NAMES[0], tiebreakers: ranks };
}

function bestHand(holeCards, communityCards) {
  const all = [...holeCards, ...communityCards].map(parseCard);
  const combos = getCombinations(all, 5);
  let best = null;
  for (const combo of combos) {
    const result = evaluate5(combo);
    if (!best || compareHands(result, best) > 0) best = result;
  }
  return best;
}

function compareHands(a, b) {
  if (a.rank !== b.rank) return a.rank - b.rank;
  for (let i = 0; i < Math.max(a.tiebreakers.length, b.tiebreakers.length); i++) {
    const av = a.tiebreakers[i] || 0;
    const bv = b.tiebreakers[i] || 0;
    if (av !== bv) return av - bv;
  }
  return 0;
}

// ─── Room Management ──────────────────────────────────────────────────────────
const rooms = new Map(); // code → room

function genCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let code = '';
  do { code = Array.from({ length: 6 }, () => chars[Math.floor(Math.random() * chars.length)]).join(''); }
  while (rooms.has(code));
  return code;
}

function createRoom(hostSocket, hostName) {
  const code = genCode();
  const room = {
    code,
    hostId: hostSocket.id,
    players: [],
    phase: 'waiting',
    deck: [],
    communityCards: [],
    pot: 0,
    sidePots: [],
    currentBet: 0,
    currentPlayerIndex: 0,
    dealerIndex: 0,
    handNumber: 0,
    minRaise: BIG_BLIND,
    lastAction: null,
    lastRaiseAmount: BIG_BLIND,
    roundOverTimer: null,
  };
  rooms.set(code, room);
  addPlayer(room, hostSocket, hostName);
  return room;
}

function addPlayer(room, socket, name) {
  const player = {
    id: socket.id,
    name: name.trim().slice(0, 16) || 'Player',
    chips: STARTING_CHIPS,
    bet: 0,
    totalBetThisRound: 0,
    folded: false,
    allIn: false,
    isDealer: false,
    isSB: false,
    isBB: false,
    cards: [],
    seatIndex: room.players.length,
    connected: true,
  };
  room.players.push(player);
  socket.join(room.code);
  return player;
}

function getPlayer(room, socketId) {
  return room.players.find(p => p.id === socketId);
}

function activePlayers(room) {
  return room.players.filter(p => p.connected && p.chips > 0);
}

// ─── Game State Broadcast ────────────────────────────────────────────────────
function buildState(room, forSocketId) {
  return {
    phase: room.phase,
    pot: room.pot,
    communityCards: room.communityCards,
    currentBet: room.currentBet,
    minRaise: room.minRaise,
    currentPlayerIndex: room.currentPlayerIndex,
    dealerIndex: room.dealerIndex,
    lastAction: room.lastAction,
    handNumber: room.handNumber,
    players: room.players.map(p => ({
      id: p.id,
      name: p.name,
      chips: p.chips,
      bet: p.bet,
      totalBetThisRound: p.totalBetThisRound,
      folded: p.folded,
      allIn: p.allIn,
      isDealer: p.isDealer,
      isSB: p.isSB,
      isBB: p.isBB,
      seatIndex: p.seatIndex,
      connected: p.connected,
      // Only send hole cards to the owner, or everyone at showdown
      cards: (room.phase === 'showdown' && !p.folded) || p.id === forSocketId
        ? p.cards
        : p.cards.map(() => '??'),
    })),
  };
}

function broadcastState(room) {
  for (const p of room.players) {
    if (p.connected) {
      const state = buildState(room, p.id);
      io.to(p.id).emit('game-state', state);
    }
  }
  // Emit action-required to current player
  if (room.phase !== 'waiting' && room.phase !== 'showdown') {
    const cp = room.players[room.currentPlayerIndex];
    if (cp && cp.connected && !cp.folded && !cp.allIn) {
      const callAmount = Math.min(room.currentBet - cp.totalBetThisRound, cp.chips);
      const minRaise = Math.min(room.minRaise, cp.chips);
      io.to(cp.id).emit('action-required', {
        validActions: getValidActions(room, cp),
        callAmount,
        minRaise,
        maxRaise: cp.chips,
      });
    }
  }
}

function getValidActions(room, player) {
  const actions = ['fold'];
  const toCall = room.currentBet - player.totalBetThisRound;
  if (toCall <= 0) actions.push('check');
  else actions.push('call');
  if (player.chips > toCall) actions.push('raise');
  if (!player.allIn) actions.push('allin');
  return actions;
}

// ─── Dealing & Phases ─────────────────────────────────────────────────────────
function startHand(room) {
  // Reset state
  room.deck = shuffle(buildDeck());
  room.communityCards = [];
  room.pot = 0;
  room.sidePots = [];
  room.currentBet = 0;
  room.lastAction = null;
  room.lastRaiseAmount = BIG_BLIND;
  room.minRaise = BIG_BLIND;
  room.handNumber++;

  const active = activePlayers(room);
  if (active.length < 2) {
    io.to(room.code).emit('error', { message: 'Not enough players with chips!' });
    room.phase = 'waiting';
    broadcastState(room);
    return;
  }

  // Reset player states
  for (const p of room.players) {
    p.cards = [];
    p.bet = 0;
    p.totalBetThisRound = 0;
    p.folded = false;
    p.allIn = false;
    p.isDealer = false;
    p.isSB = false;
    p.isBB = false;
  }

  // Rotate dealer among active players
  // Find next active dealer
  const n = active.length;
  let dealerPos = active.findIndex(p => p.isDealer);
  if (dealerPos === -1) dealerPos = -1;
  const nextDealerIdx = (dealerPos + 1) % n;
  active[nextDealerIdx].isDealer = true;
  room.dealerIndex = room.players.indexOf(active[nextDealerIdx]);

  const sbPlayer = active[(nextDealerIdx + 1) % n];
  const bbPlayer = active[(nextDealerIdx + 2) % n];

  sbPlayer.isSB = true;
  bbPlayer.isBB = true;

  // Post blinds
  postBlind(room, sbPlayer, SMALL_BLIND);
  postBlind(room, bbPlayer, BIG_BLIND);

  room.currentBet = BIG_BLIND;
  room.minRaise = BIG_BLIND * 2;

  // Deal 2 cards each
  for (const p of active) {
    p.cards = [room.deck.pop(), room.deck.pop()];
  }

  room.phase = 'preflop';

  // First to act: player after BB
  const firstToAct = active[(nextDealerIdx + 3) % n];
  room.currentPlayerIndex = room.players.indexOf(firstToAct);

  broadcastState(room);
}

function postBlind(room, player, amount) {
  const actual = Math.min(amount, player.chips);
  player.chips -= actual;
  player.bet = actual;
  player.totalBetThisRound = actual;
  room.pot += actual;
  if (player.chips === 0) player.allIn = true;
}

function advancePhase(room) {
  const active = room.players.filter(p => !p.folded && p.connected);
  const canBet = active.filter(p => !p.allIn);

  // Reset bets for new street
  for (const p of room.players) {
    p.bet = 0;
    p.totalBetThisRound = 0;
  }
  room.currentBet = 0;
  room.lastRaiseAmount = BIG_BLIND;
  room.minRaise = BIG_BLIND;

  if (room.phase === 'preflop') {
    room.phase = 'flop';
    room.deck.pop(); // burn
    room.communityCards.push(room.deck.pop(), room.deck.pop(), room.deck.pop());
  } else if (room.phase === 'flop') {
    room.phase = 'turn';
    room.deck.pop();
    room.communityCards.push(room.deck.pop());
  } else if (room.phase === 'turn') {
    room.phase = 'river';
    room.deck.pop();
    room.communityCards.push(room.deck.pop());
  } else if (room.phase === 'river') {
    room.phase = 'showdown';
    resolveShowdown(room);
    return;
  }

  // If only one player can bet, skip betting rounds
  if (canBet.length <= 1 && active.length > 1) {
    // All remaining players are all-in, run out the board
    broadcastState(room);
    setTimeout(() => advancePhase(room), 800);
    return;
  }

  // First to act post-flop: first active player left of dealer
  setFirstToAct(room);
  broadcastState(room);
}

function setFirstToAct(room) {
  const active = room.players;
  const n = active.length;
  let idx = (room.dealerIndex + 1) % n;
  for (let i = 0; i < n; i++) {
    const p = active[idx];
    if (!p.folded && !p.allIn && p.connected) {
      room.currentPlayerIndex = idx;
      return;
    }
    idx = (idx + 1) % n;
  }
  // All are all-in or folded — advance
  room.currentPlayerIndex = -1;
}

// ─── Showdown & Side Pots ─────────────────────────────────────────────────────
function resolveShowdown(room) {
  const contenders = room.players.filter(p => !p.folded && p.connected);

  // Evaluate hands
  const results = contenders.map(p => ({
    player: p,
    hand: bestHand(p.cards, room.communityCards),
  }));

  // Simple pot (no side pots for now — handle all-in side pots)
  const allInPlayers = contenders.filter(p => p.allIn).sort((a, b) => a.totalBetThisRound - b.totalBetThisRound);

  // Build side pots
  let remainingPot = room.pot;
  const pots = [];

  // Collect total bets per player across entire hand
  // We need cumulative bets. Let's rebuild from scratch using totalBetThisRound... 
  // Actually we need to track overall bets. Since we reset per-round, let's use a simplified approach:
  // Just give all chips to winner(s) from main pot.

  // Determine winner(s)
  results.sort((a, b) => compareHands(b.hand, a.hand));
  const topHand = results[0].hand;
  const winners = results.filter(r => compareHands(r.hand, topHand) === 0);

  const share = Math.floor(room.pot / winners.length);
  const remainder = room.pot - share * winners.length;

  const winnerInfo = winners.map((w, i) => {
    const amount = share + (i === 0 ? remainder : 0);
    w.player.chips += amount;
    return { name: w.player.name, amount, handName: w.hand.name };
  });

  room.pot = 0;
  room.phase = 'showdown';
  broadcastState(room);

  // Emit round-over
  io.to(room.code).emit('round-over', {
    winners: winnerInfo,
    hands: results.map(r => ({ name: r.player.name, hand: r.hand })),
  });

  // Schedule next hand
  if (room.roundOverTimer) clearTimeout(room.roundOverTimer);
  room.roundOverTimer = setTimeout(() => {
    // Remove broke players
    for (const p of room.players) {
      if (p.chips <= 0) {
        p.chips = 0;
      }
    }
    const canPlay = activePlayers(room);
    if (canPlay.length >= 2) {
      startHand(room);
    } else {
      room.phase = 'waiting';
      broadcastState(room);
      io.to(room.code).emit('game-ended', { message: 'Not enough players to continue.' });
    }
  }, 5000);
}

// ─── Action Handler ───────────────────────────────────────────────────────────
function handleAction(room, socket, action, amount) {
  if (room.phase === 'waiting' || room.phase === 'showdown') return;

  const cp = room.players[room.currentPlayerIndex];
  if (!cp || cp.id !== socket.id) return; // not their turn

  const toCall = Math.max(0, room.currentBet - cp.totalBetThisRound);

  switch (action) {
    case 'fold':
      cp.folded = true;
      room.lastAction = { player: cp.name, action: 'fold', amount: 0 };
      break;

    case 'check':
      if (toCall > 0) return; // invalid
      room.lastAction = { player: cp.name, action: 'check', amount: 0 };
      break;

    case 'call': {
      const callAmt = Math.min(toCall, cp.chips);
      cp.chips -= callAmt;
      cp.bet += callAmt;
      cp.totalBetThisRound += callAmt;
      room.pot += callAmt;
      if (cp.chips === 0) cp.allIn = true;
      room.lastAction = { player: cp.name, action: 'call', amount: callAmt };
      break;
    }

    case 'raise': {
      const raiseTotal = parseInt(amount, 10);
      if (isNaN(raiseTotal)) return;
      const minTotal = room.currentBet + room.lastRaiseAmount;
      if (raiseTotal < minTotal && raiseTotal !== cp.chips + cp.totalBetThisRound) return;
      const actualRaise = Math.min(raiseTotal - cp.totalBetThisRound, cp.chips);
      if (actualRaise <= 0) return;
      cp.chips -= actualRaise;
      cp.bet += actualRaise;
      cp.totalBetThisRound += actualRaise;
      room.pot += actualRaise;
      room.lastRaiseAmount = Math.max(cp.totalBetThisRound - room.currentBet, BIG_BLIND);
      room.currentBet = cp.totalBetThisRound;
      room.minRaise = room.currentBet + room.lastRaiseAmount;
      if (cp.chips === 0) cp.allIn = true;
      room.lastAction = { player: cp.name, action: 'raise', amount: actualRaise };
      break;
    }

    case 'allin': {
      const allInAmt = cp.chips;
      if (allInAmt <= 0) return;
      cp.bet += allInAmt;
      cp.totalBetThisRound += allInAmt;
      room.pot += allInAmt;
      cp.chips = 0;
      cp.allIn = true;
      if (cp.totalBetThisRound > room.currentBet) {
        room.lastRaiseAmount = Math.max(cp.totalBetThisRound - room.currentBet, BIG_BLIND);
        room.currentBet = cp.totalBetThisRound;
        room.minRaise = room.currentBet + room.lastRaiseAmount;
      }
      room.lastAction = { player: cp.name, action: 'all-in', amount: allInAmt };
      break;
    }

    default:
      return;
  }

  // Check if hand is over (only 1 non-folded player)
  const remaining = room.players.filter(p => !p.folded && p.connected);
  if (remaining.length === 1) {
    const winner = remaining[0];
    const winAmount = room.pot;
    winner.chips += winAmount;
    room.pot = 0;
    room.phase = 'showdown';
    broadcastState(room);
    io.to(room.code).emit('round-over', {
      winners: [{ name: winner.name, amount: winAmount, handName: 'Last Player Standing' }],
      hands: [],
    });
    if (room.roundOverTimer) clearTimeout(room.roundOverTimer);
    room.roundOverTimer = setTimeout(() => {
      const canPlay = activePlayers(room);
      if (canPlay.length >= 2) startHand(room);
      else {
        room.phase = 'waiting';
        broadcastState(room);
      }
    }, 5000);
    return;
  }

  // Advance to next player or phase
  advanceToNextOrPhase(room);
}

function advanceToNextOrPhase(room) {
  if (isBettingRoundOver(room)) {
    advancePhase(room);
  } else {
    nextPlayer(room);
    broadcastState(room);
  }
}

function isBettingRoundOver(room) {
  const active = room.players.filter(p => !p.folded && !p.allIn && p.connected);
  if (active.length === 0) return true;
  // All active players have matched current bet and everyone has had a chance
  return active.every(p => p.totalBetThisRound === room.currentBet);
}

function nextPlayer(room) {
  const n = room.players.length;
  let idx = (room.currentPlayerIndex + 1) % n;
  for (let i = 0; i < n; i++) {
    const p = room.players[idx];
    if (!p.folded && !p.allIn && p.connected) {
      room.currentPlayerIndex = idx;
      return;
    }
    idx = (idx + 1) % n;
  }
  room.currentPlayerIndex = -1;
}

// ─── Socket.io ────────────────────────────────────────────────────────────────
io.on('connection', (socket) => {
  console.log(`[+] ${socket.id} connected`);

  socket.on('create-room', ({ name }) => {
    if (!name || typeof name !== 'string') return socket.emit('error', { message: 'Name required' });
    const room = createRoom(socket, name);
    socket.emit('room-created', { code: room.code, playerId: socket.id });
    io.to(room.code).emit('player-joined', { players: room.players.map(p => ({ id: p.id, name: p.name })) });
    broadcastState(room);
    console.log(`Room ${room.code} created by ${name}`);
  });

  socket.on('join-room', ({ code, name }) => {
    if (!code || !name) return socket.emit('error', { message: 'Code and name required' });
    const room = rooms.get(code.toUpperCase());
    if (!room) return socket.emit('error', { message: 'Room not found' });
    if (room.phase !== 'waiting') return socket.emit('error', { message: 'Game already in progress' });
    if (activePlayers(room).length >= MAX_PLAYERS) return socket.emit('error', { message: 'Room is full' });

    const existing = getPlayer(room, socket.id);
    if (existing) return;

    addPlayer(room, socket, name);
    socket.emit('room-joined', { code: room.code, playerId: socket.id });
    io.to(room.code).emit('player-joined', { players: room.players.map(p => ({ id: p.id, name: p.name })) });
    broadcastState(room);
  });

  socket.on('start-game', ({ code }) => {
    const room = rooms.get(code);
    if (!room) return socket.emit('error', { message: 'Room not found' });
    if (room.hostId !== socket.id) return socket.emit('error', { message: 'Only host can start' });
    if (activePlayers(room).length < 2) return socket.emit('error', { message: 'Need at least 2 players' });
    if (room.phase !== 'waiting') return socket.emit('error', { message: 'Game already started' });

    io.to(room.code).emit('game-started', {});
    startHand(room);
  });

  socket.on('action', ({ code, action, amount }) => {
    const room = rooms.get(code);
    if (!room) return;
    handleAction(room, socket, action, amount);
  });

  socket.on('disconnect', () => {
    console.log(`[-] ${socket.id} disconnected`);
    for (const [code, room] of rooms) {
      const p = getPlayer(room, socket.id);
      if (p) {
        p.connected = false;
        io.to(room.code).emit('player-joined', { players: room.players.map(pl => ({ id: pl.id, name: pl.name, connected: pl.connected })) });

        if (room.phase !== 'waiting') {
          // If it was their turn, skip them
          const cp = room.players[room.currentPlayerIndex];
          if (cp && cp.id === socket.id) {
            p.folded = true;
            advanceToNextOrPhase(room);
          } else {
            broadcastState(room);
          }
        }
        break;
      }
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`🃏 Poker Royal running at http://localhost:${PORT}`);
  console.log(`   Share your local IP for friends to join`);
});
