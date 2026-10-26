import pygame
import sys
import random
import re
import math
from collections import deque
import os
from itertools import groupby

# ask Android for landscape (ignored on platforms that don't use it)
os.environ.setdefault("SDL_HINT_ORIENTATIONS", "LandscapeLeft LandscapeRight")

pygame.init()
pygame.font.init()

# --- Screen (what you see) and World (the big map) ---
def pick_logical_size(dw, dh):
    # Keep the real screen's shape so nothing is letterboxed or left blank.
    if dw <= 0 or dh <= 0:
        return 1280, 720
    if dw >= dh:
        return min(1800, int(720 * dw / dh)), 720
    return 720, min(1800, int(720 * dh / dw))


try:
    _info = pygame.display.Info()
    SCREEN_WIDTH, SCREEN_HEIGHT = pick_logical_size(_info.current_w, _info.current_h)
except Exception:
    SCREEN_WIDTH, SCREEN_HEIGHT = 1280, 720
WORLD_W = 1440
WORLD_H = 2560


def make_screen():
    try:
        return pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SCALED)
    except Exception:
        return pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))


screen = make_screen()
pygame.display.set_caption("World War Dots")
FONT = pygame.font.SysFont("sans-serif", 40, bold=True)
FONT_BIG = pygame.font.SysFont("sans-serif", 84, bold=True)
FONT_MID = pygame.font.SysFont("sans-serif", 48, bold=True)
FONT_SMALL = pygame.font.SysFont("sans-serif", 30)
FONT_TINY = pygame.font.SysFont("sans-serif", 26)

BG_COLOR = (0, 0, 0)
RED = (255, 50, 50)
BLUE = (0, 120, 255)
WHITE = (255, 255, 255)
BORDER_COLOR = (45, 45, 55)
GREEN = (80, 255, 120)
SELECT_COLOR = (255, 230, 60)

# --- Tuning ---
HIT_RADIUS = 30           # circular zone around each dot that claims land
CELL = 4                  # territory grid resolution (smaller = finer border, slower)
ISLAND_LIMIT = 12000      # max cells checked when testing if a dot is surrounded
START_DOTS = 15           # starting dots per side
START_TANKS = 5           # starting tanks per side (placed just behind the infantry line)
TOUCH_GRAB = 32           # finger tolerance (screen px)
COMBAT_DAMAGE = 25.0
HEAL_RATE = 0.08          # fraction of max health restored per second inside your own city
CAPTURE_TIME = 5.0
CAPTURE_NEARBY = 160
PATH_POINT_SPACING = 18
AI_SPAWN_INTERVAL = 2.0      # how often the AI commander thinks (seconds)
AI_START_DELAY = 40.0        # no attacks until this many seconds into the match
AI_DOTS_PER_TICK = 2
AI_AVOID_RADIUS = 110     # AI routes try to stay this far from enemy dots
CITY_COLS = 3
CITY_ROWS = 2             # 3 x 2 = 6 cities per side, always
ZOOM_MIN = 0.5
ZOOM_MAX = 2.0
ZOOM_STEP = 1.25
TAP_SLOP = 12             # finger movement (screen px) still counted as a tap
POINTS_PER_CITY = 1       # points a level-1 city gives per payout (level N gives N times this)
MAX_LEVEL = 3
UPGRADE_COSTS = {2: 70, 3: 140}    # points to upgrade a city TO that level
INFANTRY_COST = 10        # points to spawn an infantry
TANK_COST = 30            # points to spawn a tank
POINT_INTERVAL = 5.0     # seconds between payouts (try 3.0 for a faster economy)

STARTING_MID_Y = WORLD_H / 2

# --- Camera: centred on a world point; the map turns in 90-degree steps ---
zoom = 0.7
rot = 1 if SCREEN_WIDTH >= SCREEN_HEIGHT else 0   # quarter turns clockwise (1 = landscape, Red on the left)
cam_cx = WORLD_W / 2
cam_cy = WORLD_H * 0.62


def rot_vec(dx, dy):
    if rot == 0:
        return dx, dy
    if rot == 1:
        return -dy, dx
    if rot == 2:
        return -dx, -dy
    return dy, -dx


def unrot_vec(vx, vy):
    if rot == 0:
        return vx, vy
    if rot == 1:
        return vy, -vx
    if rot == 2:
        return -vx, -vy
    return -vy, vx


def clamp_camera():
    global cam_cx, cam_cy
    if rot % 2 == 0:
        hx, hy = SCREEN_WIDTH / 2 / zoom, SCREEN_HEIGHT / 2 / zoom
    else:
        hx, hy = SCREEN_HEIGHT / 2 / zoom, SCREEN_WIDTH / 2 / zoom
    if 2 * hx >= WORLD_W:
        cam_cx = WORLD_W / 2
    else:
        cam_cx = max(hx, min(WORLD_W - hx, cam_cx))
    if 2 * hy >= WORLD_H:
        cam_cy = WORLD_H / 2
    else:
        cam_cy = max(hy, min(WORLD_H - hy, cam_cy))


def w2s(x, y):
    vx, vy = rot_vec(x - cam_cx, y - cam_cy)
    return (SCREEN_WIDTH / 2 + vx * zoom, SCREEN_HEIGHT / 2 + vy * zoom)


def s2w(x, y):
    dx, dy = unrot_vec((x - SCREEN_WIDTH / 2) / zoom, (y - SCREEN_HEIGHT / 2) / zoom)
    return (cam_cx + dx, cam_cy + dy)


def set_zoom(new_zoom, fx, fy):
    """Zoom keeping the world point under screen pos (fx, fy) fixed."""
    global zoom, cam_cx, cam_cy
    wx, wy = s2w(fx, fy)
    zoom = max(ZOOM_MIN, min(ZOOM_MAX, new_zoom))
    dx, dy = unrot_vec((fx - SCREEN_WIDTH / 2) / zoom, (fy - SCREEN_HEIGHT / 2) / zoom)
    cam_cx = wx - dx
    cam_cy = wy - dy
    clamp_camera()


def rotate_view():
    global rot
    rot = (rot + 1) % 4
    clamp_camera()


def on_screen(x, y, margin=60):
    sx, sy = w2s(x, y)
    return -margin <= sx <= SCREEN_WIDTH + margin and -margin <= sy <= SCREEN_HEIGHT + margin


clamp_camera()


def clamp_x(x, r=10):
    return max(r, min(WORLD_W - r, x))


def clamp_y(y, r=10):
    return max(r, min(WORLD_H - r, y))


def dist(ax, ay, bx, by):
    return math.hypot(ax - bx, ay - by)


# --- Terrain: 0 grass, 1 river (slow), 2 mountain (slow, +25% defence), 3 bridge (normal) ---
TERRAIN = bytearray()          # filled in once the grid size is known
RIVER, MOUNTAIN, BRIDGE, FOREST = 1, 2, 3, 4


def terrain_at(x, y):
    if not TERRAIN:
        return 0
    gx = max(0, min(GW - 1, int(x // CELL)))
    gy = max(0, min(GH - 1, int(y // CELL)))
    return TERRAIN[gy * GW + gx]


def terrain_speed(x, y, kind='infantry'):
    t = terrain_at(x, y)
    if t == RIVER:
        return 0.5
    if t == MOUNTAIN:
        return 0.6
    if t == FOREST and kind == 'tank':      # forests only slow tanks
        return 0.5
    return 1.0


def terrain_defense(u):
    return 0.75 if terrain_at(u.x, u.y) == MOUNTAIN else 1.0


class City:
    def __init__(self, x, y, team):
        self.rect = pygame.Rect(x, y, 60, 60)
        self.team = team
        self.capture_timer = 0.0
        self.is_contested = False
        self.level = 1

    def draw(self, surface):
        if not on_screen(self.rect.centerx, self.rect.centery, 100):
            return
        cx, cy = w2s(self.rect.centerx, self.rect.centery)
        size = max(4, int(60 * zoom))
        r = pygame.Rect(0, 0, size, size)
        r.center = (int(cx), int(cy))
        color = RED if self.team == 'red' else BLUE
        pygame.draw.rect(surface, color, r, border_radius=max(2, int(8 * zoom)))
        pygame.draw.rect(surface, WHITE, r, 2, border_radius=max(2, int(8 * zoom)))
        if self.capture_timer > 0:
            frac = min(self.capture_timer / CAPTURE_TIME, 1.0)
            bar = pygame.Rect(r.x, r.bottom + 4, r.w, max(3, int(6 * zoom)))
            pygame.draw.rect(surface, (60, 60, 60), bar)
            pygame.draw.rect(surface, GREEN, (bar.x, bar.y, int(bar.w * frac), bar.h))


class Infantry:
    def __init__(self, x, y, team, path=None):
        self.x = float(x)
        self.y = float(y)
        self.team = team
        self.radius = 10
        self.max_health = 100
        self.health = 100
        self.speed = 1.5
        self.path = list(path) if path else []
        self.influence_radius = 80
        self.in_combat = False
        self.last_paint = None
        self.retreating = False
        self.damage = COMBAT_DAMAGE      # health taken off an enemy per second in a fight
        self.kind = 'infantry'
        self.ai_role = None        # AI bookkeeping: None | 'garrison' | 'squad'
        self.ai_city = None
        self.ai_squad = None
        self.ai_lock = 0.0

    def update_move(self, dt):
        if not self.in_combat:
            self.retreating = False          # broke away from the fight
        if (self.in_combat and not self.retreating) or not self.path:
            return
        tx, ty = self.path[0]
        d = dist(self.x, self.y, tx, ty)
        step = self.speed * 60 * dt * terrain_speed(self.x, self.y, self.kind)   # rivers / mountains / forests slow you
        if d <= step:
            self.x, self.y = tx, ty
            self.path.pop(0)
        else:
            self.x += (tx - self.x) / d * step
            self.y += (ty - self.y) / d * step
        self.x = clamp_x(self.x, self.radius)
        self.y = clamp_y(self.y, self.radius)

    def draw(self, surface):
        color = RED if self.team == 'red' else BLUE
        if self.path and self.team == 'red':      # Blue's routes stay hidden
            pts = [w2s(self.x, self.y)] + [w2s(px, py) for px, py in self.path]
            if len(pts) > 1:
                pygame.draw.lines(surface, color, False, pts, 2)
        if not on_screen(self.x, self.y):
            return
        sx, sy = w2s(self.x, self.y)
        rad = max(3, int(self.radius * zoom))
        pygame.draw.circle(surface, color, (int(sx), int(sy)), rad)
        pygame.draw.circle(surface, WHITE, (int(sx), int(sy)), rad, 2)
        if self.kind == 'tank':
            arm = max(2, int(rad * 0.65))
            thick = max(2, int(3 * zoom))
            pygame.draw.line(surface, (0, 0, 0), (int(sx) - arm, int(sy)),
                             (int(sx) + arm, int(sy)), thick)
            pygame.draw.line(surface, (0, 0, 0), (int(sx), int(sy) - arm),
                             (int(sx), int(sy) + arm), thick)
        w = max(14, int(self.radius * 2.4 * zoom))
        frac = max(self.health, 0) / self.max_health
        bx = int(sx - w / 2)
        by = int(sy - rad - 8)
        pygame.draw.rect(surface, (60, 60, 60), (bx, by, w, 4))
        pygame.draw.rect(surface, GREEN, (bx, by, int(w * frac), 4))


class Tank(Infantry):
    """Bigger, double health and damage, 30% slower than infantry."""

    def __init__(self, x, y, team, path=None):
        Infantry.__init__(self, x, y, team, path)
        self.kind = 'tank'
        self.radius = 14
        self.max_health = 200
        self.health = 200
        self.speed = self.speed * 0.7
        self.damage = COMBAT_DAMAGE * 2


# --- Map setup: cities scattered across each side's own territory ---
def scatter(cols, rows, y_min, y_max, team):
    """Exactly cols*rows cities: one random spot per grid cell, so always
    the same count and always spread across the whole side."""
    out = []
    cell_w = (WORLD_W - 140) / cols
    cell_h = (y_max - y_min) / rows
    pad = 30
    for c in range(cols):
        for r in range(rows):
            for _ in range(300):         # keep cities off rivers and mountains
                x = 40 + c * cell_w + random.randint(pad, int(cell_w) - 60 - pad)
                y = y_min + r * cell_h + random.randint(pad, int(cell_h) - 60 - pad)
                if (terrain_at(x, y) == 0 and terrain_at(x + 60, y + 60) == 0
                        and terrain_at(x + 30, y + 30) == 0):
                    break
            out.append(City(int(x), int(y), team))
    return out


cities = []
cities += scatter(CITY_COLS, CITY_ROWS, 100, int(STARTING_MID_Y) - 300, 'blue')
cities += scatter(CITY_COLS, CITY_ROWS, int(STARTING_MID_Y) + 240, WORLD_H - 100, 'red')

# --- Territory: a grid of cells owned by Blue or Red. Dots claim the land
# under their circular hitbox permanently, until an enemy dot claims it back.
# The border line is just where Red cells meet Blue cells.
GW = WORLD_W // CELL
GH = WORLD_H // CELL
OWN_BLUE, OWN_RED = 0, 1
# the same light-green grass on both sides; the border line shows who owns what
GRASS_COLOR = (120, 200, 120)
TERR_COLORS = {OWN_BLUE: GRASS_COLOR, OWN_RED: GRASS_COLOR}
TERRAIN = bytearray(GW * GH)
RIVER_COLOR = (45, 110, 200)       # water
MOUNTAIN_COLOR = (125, 125, 130)   # grey rock
BRIDGE_COLOR = (140, 100, 60)      # brown wood
FOREST_COLOR = (45, 115, 60)       # dark green trees


def blend(a, b, t):
    return tuple(int(a[i] * (1 - t) + b[i] * t) for i in range(3))


# terrain colour with a hint of the owner's land colour mixed in
TERRAIN_TINTS = {(o, t): blend(TERR_COLORS[o], col, amount)
                 for o in (OWN_BLUE, OWN_RED)
                 for t, col, amount in ((RIVER, RIVER_COLOR, 0.85),
                                        (MOUNTAIN, MOUNTAIN_COLOR, 0.85),
                                        (BRIDGE, BRIDGE_COLOR, 0.95),
                                        (FOREST, FOREST_COLOR, 0.95))}

EDGE_ON = BORDER_COLOR + (255,)
EDGE_OFF = BORDER_COLOR + (0,)

owner = [[OWN_BLUE] * GW for _ in range(GH)]
terr = pygame.Surface((GW, GH), 0, 32)
edge_surf = pygame.Surface((GW, GH), pygame.SRCALPHA, 32)


def refresh_cell(gx, gy):
    o = owner[gy][gx]
    is_edge = ((gx > 0 and owner[gy][gx - 1] != o)
               or (gx < GW - 1 and owner[gy][gx + 1] != o)
               or (gy > 0 and owner[gy - 1][gx] != o)
               or (gy < GH - 1 and owner[gy + 1][gx] != o))
    t = TERRAIN[gy * GW + gx]
    base = TERRAIN_TINTS[(o, t)] if t else TERR_COLORS[o]
    terr.set_at((gx, gy), BORDER_COLOR if is_edge else base)


terr.fill(TERR_COLORS[OWN_BLUE])
edge_surf.fill(EDGE_OFF)
start_rows = []
for gx in range(GW):
    by = STARTING_MID_Y + 12 * math.sin(gx * CELL * 0.012)
    yb = max(0, min(GH, int((by - CELL / 2) // CELL) + 1))
    start_rows.append(yb)
    for gy in range(yb, GH):
        owner[gy][gx] = OWN_RED
    terr.fill(TERR_COLORS[OWN_RED], (gx, yb, 1, GH - yb))
for gx in range(GW):
    yb = start_rows[gx]
    for gy in range(max(0, yb - 3), min(GH, yb + 3)):
        refresh_cell(gx, gy)

clock = pygame.time.Clock()
active_units = []

# Starting line of Red + Blue dots near the border
for i in range(START_DOTS):
    sx = 72 + i * (WORLD_W - 144) / (START_DOTS - 1)
    active_units.append(Infantry(sx, STARTING_MID_Y + 70, 'red'))
    active_units.append(Infantry(sx, STARTING_MID_Y - 70, 'blue'))
for i in range(START_TANKS):
    tx = 200 + i * (WORLD_W - 400) / (START_TANKS - 1)
    active_units.append(Tank(tx, STARTING_MID_Y + 130, 'red'))
    active_units.append(Tank(tx, STARTING_MID_Y - 130, 'blue'))

# (no spawn timers: both sides now buy units with points)

# Input state
dragging_unit = None
selected_unit = None      # the red dot you tapped; only this one can be given a path
selected_city = None      # the red city you tapped; its panel (spawn / upgrade) is open
tap_city = None           # city under the finger when a tap started
points = 0                # your points (earned from your cities, spent on stuff later)
point_timer = 0.0         # counts up to the next payout
ai_points = 0             # the AI's (Blue's) points: same income, same prices
ai_next_tank = None       # AI's plan for its next purchase (True = saving for a tank)
drag_points = []
panning = False
pan_last = (0, 0)
pan_start = (0, 0)
pan_moved = False
fingers = {}
pinching = False
pinch_last = None
ai_timer = 0.0

def layout_buttons():
    global ZOOM_IN_RECT, ZOOM_OUT_RECT, ROTATE_RECT, PAUSE_RECT
    PAUSE_RECT = pygame.Rect(20, 40, 60, 60)
    ZOOM_IN_RECT = pygame.Rect(SCREEN_WIDTH - 80, 40, 60, 60)
    ZOOM_OUT_RECT = pygame.Rect(SCREEN_WIDTH - 80, 110, 60, 60)
    ROTATE_RECT = pygame.Rect(SCREEN_WIDTH - 80, 180, 60, 60)


layout_buttons()


def on_window_resize(w, h):
    # The phone was turned: re-fit to the new shape and keep the map's long
    # side along the screen's long side.
    global SCREEN_WIDTH, SCREEN_HEIGHT, screen, rot, terr_cache
    nw, nh = pick_logical_size(w, h)
    if (nw >= nh) == (SCREEN_WIDTH >= SCREEN_HEIGHT):
        return
    SCREEN_WIDTH, SCREEN_HEIGHT = nw, nh
    screen = make_screen()
    layout_buttons()
    rot = (rot + 1) % 4 if nw >= nh else (rot - 1) % 4
    terr_cache = None
    clamp_camera()


terr_dirty = True
terr_cache = None
terr_cache_pos = (0, 0)
terr_cache_key = None
terr_cache_grid = (0, 0, 0, 0, 0, 0)   # gx0, gy0, w, h, dw, dh
dirty_box = None                        # [gx_min, gy_min, gx_max, gy_max] of changed cells


terr_cam_key = None        # camera state the cached image was built for
terr_land_ver = -1         # land version the cached image was built for
terr_last_build = 0        # when it was last rebuilt (ms)
TERR_REFRESH_MS = 100      # land changes redraw the map at most this often
land_version = 0           # bumps whenever any land changes owner


def view_world_box():
    pts = [s2w(0, 0), s2w(SCREEN_WIDTH, 0), s2w(0, SCREEN_HEIGHT),
           s2w(SCREEN_WIDTH, SCREEN_HEIGHT)]
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    return min(xs), min(ys), max(xs), max(ys)


def build_territory_image():
    # Only the visible slice of the small territory map is rotated and scaled
    # (one scale per rebuild), so panning and zooming stay cheap.
    global terr_cache, terr_cache_pos
    bx0, by0, bx1, by1 = view_world_box()
    gx0 = max(0, int(bx0 // CELL))
    gy0 = max(0, int(by0 // CELL))
    gx1 = min(GW, int(bx1 // CELL) + 2)
    gy1 = min(GH, int(by1 // CELL) + 2)
    w, h = gx1 - gx0, gy1 - gy0
    if w <= 0 or h <= 0:
        terr_cache = None
        return
    sub = terr.subsurface(pygame.Rect(gx0, gy0, w, h))
    if rot:
        sub = pygame.transform.rotate(sub, -90 * rot)
    corners = [w2s(gx0 * CELL, gy0 * CELL), w2s(gx1 * CELL, gy0 * CELL),
               w2s(gx0 * CELL, gy1 * CELL), w2s(gx1 * CELL, gy1 * CELL)]
    minx = min(c[0] for c in corners)
    miny = min(c[1] for c in corners)
    dw = max(1, int(round(max(c[0] for c in corners) - minx)))
    dh = max(1, int(round(max(c[1] for c in corners) - miny)))
    terr_cache = pygame.transform.scale(sub, (dw, dh))     # crisp, no blur
    terr_cache_pos = (minx, miny)


def draw_territory():
    # The map image is rebuilt straight away when the camera moves, but when
    # only the land changed (fighting) it is refreshed at most every 100 ms.
    # Always the same crisp scale, so the picture never switches look.
    global terr_cam_key, terr_land_ver, terr_last_build
    now = pygame.time.get_ticks()
    cam_key = (round(cam_cx, 1), round(cam_cy, 1), zoom, rot)
    if terr_cache is None or cam_key != terr_cam_key:
        build_territory_image()
    elif land_version != terr_land_ver and now - terr_last_build >= TERR_REFRESH_MS:
        build_territory_image()
    else:
        cam_key = None
    if cam_key is not None:
        terr_cam_key = cam_key
        terr_land_ver = land_version
        terr_last_build = now
    if terr_cache is not None:
        screen.blit(terr_cache, terr_cache_pos)


land_changed = True
last_scan_ms = 0
land_timer = 0.0
pending_seeds = set()     # enemy cells touching freshly claimed land (to test for cut-off pockets)
smooth_chunks = set()     # 16x16 cell chunks that changed (to clean up stray specks)
ORPHAN_LIMIT = 3000       # biggest cut-off pocket we test for
CHUNK = 16


def mark_dirty(x0, y0, x1, y1):
    global dirty_box, land_changed, land_version
    land_changed = True
    land_version += 1
    if dirty_box is None:
        dirty_box = [x0, y0, x1, y1]
    else:
        dirty_box = [min(dirty_box[0], x0), min(dirty_box[1], y0),
                     max(dirty_box[2], x1), max(dirty_box[3], y1)]


def refresh_around(gx, gy):
    refresh_cell(gx, gy)
    if gx > 0:
        refresh_cell(gx - 1, gy)
    if gx < GW - 1:
        refresh_cell(gx + 1, gy)
    if gy > 0:
        refresh_cell(gx, gy - 1)
    if gy < GH - 1:
        refresh_cell(gx, gy + 1)


def paint_dot(u):
    # Pure hitbox: the dot claims every cell inside its circle for its team.
    # Nothing is drawn between the dot and its home land, so a surrounded dot
    # just holds its own circle as it moves. A dot only repaints after it has
    # moved about a cell, which keeps this cheap.
    if u.last_paint is not None and dist(u.x, u.y, u.last_paint[0], u.last_paint[1]) < CELL:
        return False
    u.last_paint = (u.x, u.y)
    team = OWN_RED if u.team == 'red' else OWN_BLUE
    r = HIT_RADIUS
    gy0 = max(0, int((u.y - r) // CELL))
    gy1 = min(GH - 1, int((u.y + r) // CELL))
    changed = []
    for gy in range(gy0, gy1 + 1):
        cy = gy * CELL + CELL / 2
        dy = cy - u.y
        if abs(dy) > r:
            continue
        span = math.sqrt(r * r - dy * dy)
        gx0 = max(0, int(math.ceil((u.x - span - CELL / 2) / CELL)))
        gx1 = min(GW - 1, int((u.x + span - CELL / 2) // CELL))
        row = owner[gy]
        for gx in range(gx0, gx1 + 1):
            if row[gx] != team:
                row[gx] = team
                changed.append((gx, gy))
    for gx, gy in changed:
        refresh_around(gx, gy)
    if changed:
        xs = [c[0] for c in changed]
        ys = [c[1] for c in changed]
        mark_dirty(min(xs), min(ys), max(xs), max(ys))
        for cx in range(min(xs) // CHUNK, max(xs) // CHUNK + 1):
            for cy in range(min(ys) // CHUNK, max(ys) // CHUNK + 1):
                smooth_chunks.add((cx, cy))
    return bool(changed)


def surrounded_island(gx, gy, team, limit=ISLAND_LIMIT):
    """Cells of the dot's own-team pocket if it is cut off from its home
    edge (Red home = bottom, Blue home = top); None if it is connected."""
    home_row = GH - 1 if team == OWN_RED else 0
    start = gy * GW + gx
    seen = {start}
    q = deque([start])
    while q:
        idx = q.popleft()
        y, x = divmod(idx, GW)
        if y == home_row:
            return None
        for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
            if 0 <= nx < GW and 0 <= ny < GH:
                nidx = ny * GW + nx
                if nidx not in seen and owner[ny][nx] == team:
                    seen.add(nidx)
                    q.append(nidx)
        if len(seen) > limit:
            return None
    return seen


def flip_island(island, new_owner):
    for idx in island:
        y, x = divmod(idx, GW)
        owner[y][x] = new_owner
    touched = set()
    for idx in island:
        y, x = divmod(idx, GW)
        touched.add(idx)
        if x > 0:
            touched.add(idx - 1)
        if x < GW - 1:
            touched.add(idx + 1)
        if y > 0:
            touched.add(idx - GW)
        if y < GH - 1:
            touched.add(idx + GW)
    xs, ys = [], []
    for idx in touched:
        y, x = divmod(idx, GW)
        refresh_cell(x, y)
        xs.append(x)
        ys.append(y)
    mark_dirty(min(xs), min(ys), max(xs), max(ys))


def dot_died(u):
    # Strictly: a dot that dies while surrounded by enemy territory hands its
    # whole pocket of land to the enemy. Same rule for both teams.
    team = OWN_RED if u.team == 'red' else OWN_BLUE
    gx = max(0, min(GW - 1, int(u.x // CELL)))
    gy = max(0, min(GH - 1, int(u.y // CELL)))
    if owner[gy][gx] != team:
        return
    island = surrounded_island(gx, gy, team)
    if not island:
        return
    flip_island(island, OWN_BLUE if team == OWN_RED else OWN_RED)


def tidy_land():
    # Runs a few times a second.
    # 1) Border cleanup: remove stray specks and 1-cell spurs.
    chunks = list(smooth_chunks)[:12]
    for c in chunks:
        smooth_chunks.discard(c)
    for cx, cy in chunks:
        x0 = max(0, cx * CHUNK - 2)
        y0 = max(0, cy * CHUNK - 2)
        x1 = min(GW - 1, cx * CHUNK + CHUNK + 1)
        y1 = min(GH - 1, cy * CHUNK + CHUNK + 1)
        flips = []
        for y in range(y0, y1 + 1):
            row = owner[y]
            for x in range(x0, x1 + 1):
                o = row[x]
                # cheap skip: all four direct neighbours agree with this cell
                if ((x == 0 or row[x - 1] == o) and (x == GW - 1 or row[x + 1] == o)
                        and (y == 0 or owner[y - 1][x] == o)
                        and (y == GH - 1 or owner[y + 1][x] == o)):
                    continue
                diff = 0
                for ny in (y - 1, y, y + 1):
                    if 0 <= ny < GH:
                        r2 = owner[ny]
                        for nx in (x - 1, x, x + 1):
                            if (nx != x or ny != y) and 0 <= nx < GW and r2[nx] != o:
                                diff += 1
                if diff >= 6:
                    flips.append((x, y))
        for x, y in flips:
            owner[y][x] = 1 - owner[y][x]
        for x, y in flips:
            refresh_around(x, y)
        if flips:
            mark_dirty(x0, y0, x1, y1)

    # 2) Anywhere on the map: land cut off from its team's home edge with
    #    none of that team's dots on it turns to the other team.
    global land_changed, last_scan_ms
    now = pygame.time.get_ticks()
    if now - last_scan_ms >= (1500 if land_changed else 4000):
        last_scan_ms = now
        land_changed = False
        land_scan()


RUN_RE = re.compile(b'\\x00+|\\x01+')      # a run of Blue (0) or Red (1) cells


def land_scan():
    # Splits the whole map into patches of same-owner land using row runs
    # (fast), finds patches not touching their home edge (Red: bottom, Blue:
    # top), and gives the ones with no friendly dot to the other team.
    runs = []                 # [y, x0, x1, team]
    row_runs = []
    for y in range(GH):
        row = bytes(owner[y])
        ids = []
        for m in RUN_RE.finditer(row):
            ids.append(len(runs))
            runs.append((y, m.start(), m.end() - 1, row[m.start()]))
        row_runs.append(ids)
    parent = list(range(len(runs)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for y in range(1, GH):
        pa, pb = row_runs[y - 1], row_runs[y]
        i = j = 0
        while i < len(pa) and j < len(pb):
            ra, rb = runs[pa[i]], runs[pb[j]]
            if ra[3] == rb[3] and max(ra[1], rb[1]) <= min(ra[2], rb[2]):
                ra_root, rb_root = find(pa[i]), find(pb[j])
                if ra_root != rb_root:
                    parent[ra_root] = rb_root
            if ra[2] < rb[2]:
                i += 1
            else:
                j += 1

    home = set()
    for rid in row_runs[0]:
        if runs[rid][3] == OWN_BLUE:
            home.add(find(rid))
    for rid in row_runs[GH - 1]:
        if runs[rid][3] == OWN_RED:
            home.add(find(rid))

    has_dot = set()
    for u in active_units:
        gx = max(0, min(GW - 1, int(u.x // CELL)))
        gy = max(0, min(GH - 1, int(u.y // CELL)))
        team = OWN_RED if u.team == 'red' else OWN_BLUE
        for rid in row_runs[gy]:
            r = runs[rid]
            if r[1] <= gx <= r[2]:
                if r[3] == team:
                    has_dot.add(find(rid))
                break

    groups = {}
    for rid, r in enumerate(runs):
        root = find(rid)
        if root in home or root in has_dot:
            continue
        groups.setdefault(root, []).append(rid)
    for root, rids in groups.items():
        team = runs[rids[0]][3]
        cells = set()
        for rid in rids:
            y, x0, x1, _ = runs[rid]
            cells.update(range(y * GW + x0, y * GW + x1 + 1))
        flip_island(cells, 1 - team)


def update_combat(units, dt):
    for u in units:
        u.in_combat = False
    reds = [u for u in units if u.team == 'red']
    blues = [u for u in units if u.team == 'blue']
    for r in reds:
        for b in blues:
            reach = r.radius + b.radius
            if abs(r.x - b.x) > reach or abs(r.y - b.y) > reach:
                continue
            if dist(r.x, r.y, b.x, b.y) <= reach:
                r.in_combat = True
                b.in_combat = True
                r.health -= b.damage * dt * terrain_defense(r)
                b.health -= r.damage * dt * terrain_defense(b)
    for u in units:
        if u.health <= 0:
            dot_died(u)
    units[:] = [u for u in units if u.health > 0]


def update_healing(units, dt):
    # Units standing in their own city (not in a fight, city not under
    # attack) slowly heal.
    for city in cities:
        if city.is_contested:
            continue
        zone = city.rect.inflate(30, 30)
        for u in units:
            if (u.team == city.team and not u.in_combat
                    and u.health < u.max_health and zone.collidepoint(u.x, u.y)):
                u.health = min(u.max_health, u.health + u.max_health * HEAL_RATE * dt)


def update_capture(units, dt):
    for city in cities:
        enemy = 'red' if city.team == 'blue' else 'blue'
        cx, cy = city.rect.center
        attackers = [u for u in units
                     if u.team == enemy and city.rect.collidepoint(u.x, u.y)]
        defenders_near = [u for u in units
                          if u.team == city.team
                          and dist(u.x, u.y, cx, cy) <= CAPTURE_NEARBY]
        city.is_contested = bool(attackers)
        if attackers and not defenders_near:
            city.capture_timer += dt
            if city.capture_timer >= CAPTURE_TIME:
                city.team = enemy
                city.level = 1          # upgrades are lost when a city is captured
                city.capture_timer = 0.0
        else:
            city.capture_timer = 0.0


def spawn_at_city(city, unit_class):
    if city.rect.centery > STARTING_MID_Y:
        py = city.rect.top - 30
    else:
        py = city.rect.bottom + 30
    px = clamp_x(city.rect.centerx + random.randint(-35, 35))
    py = clamp_y(py)
    active_units.append(unit_class(px, py, city.team))


def buy_unit(city, unit_class, cost):
    # spend points to spawn one of your units at the city (False = can't afford)
    global points
    if points < cost:
        return False
    points -= cost
    spawn_at_city(city, unit_class)
    return True


def plan_path(sx, sy, tx, ty, foe_team='red'):
    """Route for the AI: a curve that bends around crowds of enemy dots, or a
    detour through a bridge / pass when rivers or mountains are in the way."""
    foes = [(u.x, u.y, 2 if u.kind == 'tank' else 1)
            for u in active_units if u.team == foe_team]
    length = dist(sx, sy, tx, ty)
    has_terrain = bool(terrain_cells)
    if length < 1 or (not foes and not has_terrain):
        return [(tx, ty)]

    def cost_of(pts):
        c = 0.0
        for bx, by in pts[:-1]:
            c += (1.0 - terrain_speed(bx, by)) * 200
            for fx, fy, w in foes:
                d = dist(bx, by, fx, fy)
                if d < AI_AVOID_RADIUS:
                    c += w * (1 - d / AI_AVOID_RADIUS) * 60
        return c

    def line_pts(ax, ay, bx, by):
        n = max(2, min(12, int(dist(ax, ay, bx, by) / 80)))
        return [(clamp_x(ax + (bx - ax) * k / n), clamp_y(ay + (by - ay) * k / n))
                for k in range(1, n + 1)]

    nx, ny = -(ty - sy) / length, (tx - sx) / length      # sideways direction
    steps = max(6, min(20, int(length / 80)))
    candidates = []
    for off in (0.0, -0.2, 0.2, -0.4, 0.4):
        cxp = (sx + tx) / 2 + nx * off * length
        cyp = (sy + ty) / 2 + ny * off * length
        pts = []
        for k in range(1, steps + 1):
            t = k / steps
            bx = (1 - t) ** 2 * sx + 2 * (1 - t) * t * cxp + t * t * tx
            by = (1 - t) ** 2 * sy + 2 * (1 - t) * t * cyp + t * t * ty
            pts.append((clamp_x(bx), clamp_y(by)))
        candidates.append((cost_of(pts) + abs(off) * length * 0.3, pts))
    for bx, by in map_bridges:                               # via a crossing
        pts = line_pts(sx, sy, bx, by) + line_pts(bx, by, tx, ty)
        extra = (dist(sx, sy, bx, by) + dist(bx, by, tx, ty) - length) * 0.3
        candidates.append((cost_of(pts) + extra, pts))
    return min(candidates, key=lambda c: c[0])[1]


# ---------------------------------------------------------------------------
# Strategic AI commander
#   * keeps a garrison at each city (more when enemies are near)
#   * only attacks when its squad is clearly stronger than the defenders,
#     so it waits and concentrates force instead of trickling units in
#   * squads gather first, then strike together: direct, pincer or an
#     encirclement ring around the target
#   * 1-2 squad members peel off to deal with a defender who shows up,
#     the rest carry on with the mission
#   * badly hurt units retreat to the nearest city
#   * pulls a staging squad back to defend a city that is being overrun
# ---------------------------------------------------------------------------
SQUAD_MIN = 5
SQUAD_MIN_LAND = 3
SQUAD_MAX = 14
ATTACK_RATIO = 1.3        # squad must be this much stronger than the defenders
THREAT_RANGE = 380
TARGET_RANGE = 300
INTERCEPT_RANGE = 260
MAX_INTERCEPTORS = 2
STAGE_TIMEOUT = 25.0
RING_RADIUS = 170
MAX_SQUADS = 2
RETREAT_HP = 0.2          # hurt units below this fraction of health pull back (0 = never)
ATTACK_COOLDOWN = 20.0    # minimum seconds between launching attacks
TWO_PRONG = False         # launch a second attack on another target at the same time
AI_SPAM = False           # easy mode: no tactics, just sends units at you
TACT_OPEN = (2, 3, 5)     # weights: encircle, pincer, direct (target lightly defended)
TACT_CONTESTED = (3, 7)   # weights: pincer, direct (target defended)
GARRISON_CAP = 2
AI_UPGRADE_BUDGET = 3     # total upgrade steps the AI will own at once across its cities (0 = never)
AI_TANK_SHARE = 0.25      # chance that an AI purchase is a tank
AI_SAVE_MIN_UNITS = 25    # AI saves for upgrades once it has this many units (None = never saves)
last_attack_time = -1e9

ai_squads = []


def strength(u):
    return (2.0 if u.kind == 'tank' else 1.0) * max(u.health, 0) / u.max_health


def force_near(x, y, r, team):
    return sum(strength(u) for u in active_units
               if u.team == team and dist(u.x, u.y, x, y) <= r)


class Squad:
    def __init__(self, units, xy, city, tactic):
        self.units = list(units)
        self.xy = xy
        self.city = city
        self.tactic = tactic          # 'direct' | 'pincer' | 'encircle'
        self.phase = 'stage'          # stage -> (ring ->) strike
        self.born = game_time
        self.ring_start = 0.0
        self.chasers = {}             # squad unit -> enemy it was sent after
        self.stage = {}
        self.side = {}
        for u in self.units:
            u.ai_role = 'squad'
            u.ai_squad = self
            u.ai_city = None
        self.plan_stage()

    def centroid(self):
        n = len(self.units) or 1
        return (sum(u.x for u in self.units) / n, sum(u.y for u in self.units) / n)

    def plan_stage(self):
        tx, ty = self.xy
        cx, cy = self.centroid()
        ax, ay = cx - tx, cy - ty
        length = math.hypot(ax, ay) or 1.0
        ax, ay = ax / length, ay / length          # target -> squad
        px, py = -ay, ax                           # sideways
        self.axis = (ax, ay, px, py)
        n = len(self.units)
        for i, u in enumerate(self.units):
            if self.tactic == 'direct':
                off = (i - n / 2) * 28
                sx = tx + ax * 220 + px * off
                sy = ty + ay * 220 + py * off
                self.side[u] = 0
            elif self.tactic == 'pincer':
                sd = 1 if i % 2 == 0 else -1
                self.side[u] = sd
                back = 180 + (i // 2) * 30
                sx = tx + ax * back + px * 260 * sd
                sy = ty + ay * back + py * 260 * sd
            else:                                   # encircle: a point on the ring
                ang = math.atan2(ay, ax) + i * 2 * math.pi / n
                self.side[u] = ang
                sx = tx + math.cos(ang) * RING_RADIUS
                sy = ty + math.sin(ang) * RING_RADIUS
            sx, sy = clamp_x(sx), clamp_y(sy)
            self.stage[u] = (sx, sy)
            u.path = plan_path(u.x, u.y, sx, sy)

    def arc_path(self, u):
        tx, ty = self.xy
        sweep = 2 * math.pi / max(1, len(self.units)) + 0.2
        steps = max(3, int(RING_RADIUS * sweep / 40))
        pts = []
        for k in range(1, steps + 1):
            a = self.side[u] + sweep * k / steps
            pts.append((clamp_x(tx + math.cos(a) * RING_RADIUS),
                        clamp_y(ty + math.sin(a) * RING_RADIUS)))
        return pts

    def mission_path(self, u):
        if self.phase == 'strike':
            return [self.xy]
        return [self.stage[u]]

    def start_strike(self, free):
        self.phase = 'strike'
        tx, ty = self.xy
        ax, ay, px, py = self.axis
        for u in free:
            if self.tactic == 'pincer':
                sd = self.side[u]
                u.path = [(clamp_x(tx + px * 140 * sd), clamp_y(ty + py * 140 * sd)), self.xy]
            else:
                u.path = [self.xy]

    def handle_threats(self):
        # chasers: keep after their target, or go back to the mission
        for u, foe in list(self.chasers.items()):
            if u not in self.units or foe not in active_units or foe.health <= 0:
                del self.chasers[u]
                if u in self.units:
                    u.path = self.mission_path(u)
            else:
                u.path = [(foe.x, foe.y)]
        if len(self.chasers) >= MAX_INTERCEPTORS:
            return
        members = [u for u in self.units if u not in self.chasers]
        if len(members) < 4:
            return
        cx, cy = self.centroid()
        chased = set(self.chasers.values())
        foes = [f for f in active_units if f.team == 'red' and f not in chased
                and (dist(f.x, f.y, cx, cy) <= INTERCEPT_RANGE
                     or dist(f.x, f.y, self.xy[0], self.xy[1]) <= INTERCEPT_RANGE)]
        foes.sort(key=lambda f: dist(f.x, f.y, cx, cy))
        for foe in foes:
            need = strength(foe) * 1.1
            picks = sorted(members, key=lambda m: dist(m.x, m.y, foe.x, foe.y))
            sel, total = [], 0.0
            for m in picks[:MAX_INTERCEPTORS - len(self.chasers)]:
                sel.append(m)
                total += strength(m)
                if total >= need:
                    break
            if not sel or total < need * 0.8 or len(members) - len(sel) < 3:
                continue
            for m in sel:
                self.chasers[m] = foe
                m.path = [(foe.x, foe.y)]
                members.remove(m)
            if len(self.chasers) >= MAX_INTERCEPTORS:
                break

    def update(self, alive):
        self.units = [u for u in self.units if u in alive and u.ai_squad is self]
        if not self.units:
            return
        self.handle_threats()
        free = [u for u in self.units if u not in self.chasers]
        if self.phase == 'stage':
            ready = all(dist(u.x, u.y, self.stage[u][0], self.stage[u][1]) < 90 for u in free)
            if ready or game_time - self.born > STAGE_TIMEOUT:
                if self.tactic == 'encircle':
                    self.phase = 'ring'
                    self.ring_start = game_time
                    for u in free:
                        u.path = self.arc_path(u)
                else:
                    self.start_strike(free)
        elif self.phase == 'ring':
            if all(not u.path for u in free) or game_time - self.ring_start > 20:
                self.start_strike(free)
        else:
            for u in free:
                if not u.path and not u.in_combat and dist(u.x, u.y, self.xy[0], self.xy[1]) > 60:
                    u.path = [self.xy]

    def finished(self):
        if not self.units:
            return True
        if self.city is not None and self.city.team == 'blue':
            return True
        if game_time - self.born > 120:
            return True
        if (self.city is None and self.phase == 'strike'
                and all(not u.path for u in self.units)):
            return True
        return False

    def release(self):
        for u in self.units:
            u.ai_role = None
            u.ai_squad = None
            u.path = []
        self.chasers.clear()


def ai_retreats(blues):
    # badly hurt units in a fight pull back to the nearest Blue city
    own = [c for c in cities if c.team == 'blue']
    if not own:
        return
    for u in blues:
        if (RETREAT_HP > 0 and u.in_combat and u.health < RETREAT_HP * u.max_health
                and game_time >= u.ai_lock):
            c = min(own, key=lambda c: dist(u.x, u.y, c.rect.centerx, c.rect.centery))
            u.ai_squad = None
            u.ai_role = None
            u.ai_city = None
            u.ai_lock = game_time + 8.0
            u.path = [c.rect.center]
            u.retreating = True


def ai_garrisons(blue_cities, blues, pool):
    for c in blue_cities:
        cx, cy = c.rect.center
        threat = force_near(cx, cy, THREAT_RANGE, 'red')
        want = min(GARRISON_CAP, 1 + (1 if threat > 0 else 0) + (1 if threat >= 3 else 0)
                    + (1 if threat >= 6 else 0))
        have = [u for u in blues if u.ai_role == 'garrison' and u.ai_city is c]
        for extra in have[want:]:
            extra.ai_role = None
            extra.ai_city = None
            pool.append(extra)
        need = want - len(have[:want])
        post_y = cy + (70 if cy < STARTING_MID_Y else -70)   # towards the front
        for _ in range(max(0, need)):
            if not pool:
                break
            u = min(pool, key=lambda q: dist(q.x, q.y, cx, cy))
            pool.remove(u)
            u.ai_role = 'garrison'
            u.ai_city = c
            u.path = plan_path(u.x, u.y, cx + random.randint(-30, 30), post_y)
        if need > 0 and not pool and threat > force_near(cx, cy, THREAT_RANGE, 'blue'):
            # city is being overrun: pull back a squad that hasn't struck yet
            for sq in ai_squads:
                if sq.phase == 'stage':
                    sq.release()
                    pool.extend(sq.units)
                    sq.units = []
                    break


def _form_squad(pool):
    if len(ai_squads) >= MAX_SQUADS or len(pool) < SQUAD_MIN_LAND:
        return False
    targeted = {sq.city for sq in ai_squads if sq.city is not None}
    options = []
    for c in cities:
        if c.team != 'red' or c in targeted:
            continue
        x, y = c.rect.center
        defenders = force_near(x, y, TARGET_RANGE, 'red') + 0.5 * force_near(x, y, 700, 'red')
        near = min(dist(q.x, q.y, x, y) for q in pool)
        options.append((defenders * 100 + near * 0.15, c, defenders, (x, y)))
    options.sort(key=lambda o: o[0])
    for _, c, defenders, xy in options:
        ranked = sorted(pool, key=lambda q: dist(q.x, q.y, xy[0], xy[1]))
        need = max(defenders * ATTACK_RATIO, SQUAD_MIN * 0.8)
        units, total = [], 0.0
        for q in ranked[:SQUAD_MAX]:        # keep adding until clearly stronger
            units.append(q)
            total += strength(q)
            if total >= need and len(units) >= SQUAD_MIN:
                break
        if len(units) < SQUAD_MIN or total < need:
            continue
        if len(units) == SQUAD_MIN and len(ranked) > SQUAD_MIN and random.random() < 0.7:
            units.append(ranked[SQUAD_MIN])      # one extra so pincers / rings are possible
        local = force_near(xy[0], xy[1], 220, 'red')
        if len(units) >= 6 and local <= 1.0:
            tactic = random.choices(['encircle', 'pincer', 'direct'], TACT_OPEN)[0]
        elif len(units) >= 6:
            tactic = random.choices(['pincer', 'direct'], TACT_CONTESTED)[0]
        else:
            tactic = 'direct'
        for q in units:
            pool.remove(q)
        ai_squads.append(Squad(units, xy, c, tactic))
        return True
    # no city worth attacking: retake Red land inside Blue's half
    if len(pool) < SQUAD_MIN_LAND:
        return False
    best = None
    for _ in range(80):
        gx = random.randrange(GW)
        gy = random.randrange(GH)
        y = gy * CELL + CELL / 2
        if owner[gy][gx] == OWN_RED and y < STARTING_MID_Y - 150:
            x = gx * CELL + CELL / 2
            f = force_near(x, y, 250, 'red')
            if best is None or f < best[0]:
                best = (f, x, y)
    if best is None:
        return False
    f, x, y = best
    ranked = sorted(pool, key=lambda q: dist(q.x, q.y, x, y))[:5]
    if len(ranked) >= SQUAD_MIN_LAND and sum(strength(q) for q in ranked) >= max(f * ATTACK_RATIO, 2.4):
        for q in ranked:
            pool.remove(q)
        ai_squads.append(Squad(ranked, (x, y), None, 'direct'))
        return True
    return False


def ai_plan_attack(pool):
    global last_attack_time
    if game_time < AI_START_DELAY or game_time - last_attack_time < ATTACK_COOLDOWN:
        return
    if _form_squad(pool):
        last_attack_time = game_time
        if TWO_PRONG and len(pool) >= SQUAD_MIN_LAND + 2:
            _form_squad(pool)           # a second strike on a different target


def ai_spam():
    # Easy AI: no garrisons, no tactics - it just keeps sending units at you
    idle = [u for u in active_units if u.team == 'blue' and not u.path]
    red_cities = [c for c in cities if c.team == 'red']
    for u in random.sample(idle, min(AI_DOTS_PER_TICK, len(idle))):
        if red_cities and random.random() < 0.5:
            u.path = [random.choice(red_cities).rect.center]
            continue
        best = None
        for _ in range(60):
            gx = random.randrange(GW)
            gy = random.randrange(GH)
            if owner[gy][gx] == OWN_RED:
                x = gx * CELL + CELL / 2
                y = gy * CELL + CELL / 2
                d = dist(u.x, u.y, x, y)
                if best is None or d < best[0]:
                    best = (d, x, y)
        if best:
            u.path = [(best[1], best[2])]


def ai_spend():
    """The AI buys units and upgrades with its points, using the same prices
    as you. Difficulty decides how smart it is about it:
      easy   - buys infantry the moment it can afford one, never upgrades
      medium - mixes in tanks, buys up to 3 upgrade steps (saves once it has an army)
      hard   - more tanks, buys up to 6 upgrade steps, starts saving earlier
    Under attack, it stops saving and spends on defenders at the city in danger."""
    global ai_points, ai_next_tank
    blue_cities = [c for c in cities if c.team == 'blue']
    if not blue_cities:
        return

    def danger(c):
        cx, cy = c.rect.center
        return force_near(cx, cy, THREAT_RANGE, 'red') - force_near(cx, cy, THREAT_RANGE, 'blue')

    worst = max(blue_cities, key=danger)
    threatened = danger(worst) > 0

    # upgrade: the safest city that is still below the level this AI will go to
    steps_owned = sum(c.level - 1 for c in blue_cities)
    up_cities = ([c for c in blue_cities if c.level < MAX_LEVEL]
                 if steps_owned < AI_UPGRADE_BUDGET else [])
    up_target = None
    if up_cities:
        up_target = min(up_cities, key=lambda c: (c.level, danger(c)))
        up_cost = UPGRADE_COSTS[up_target.level + 1]
        if ai_points >= up_cost and not threatened:
            ai_points -= up_cost
            up_target.level += 1
            return
        n_units = sum(1 for u in active_units if u.team == 'blue')
        if (AI_SAVE_MIN_UNITS is not None and n_units >= AI_SAVE_MIN_UNITS
                and not threatened):
            return                      # saving up for the upgrade

    # otherwise spend on units (a few per think, at the city in danger if any).
    # It decides in advance whether the next purchase is a tank and waits for
    # the points, unless a city is under threat (then it buys whatever it can).
    for _ in range(3):
        if ai_next_tank is None:
            ai_next_tank = random.random() < AI_TANK_SHARE
        if ai_next_tank and ai_points >= TANK_COST:
            cls, cost = Tank, TANK_COST
        elif (not ai_next_tank or threatened) and ai_points >= INFANTRY_COST:
            cls, cost = Infantry, INFANTRY_COST
        else:
            break
        ai_points -= cost
        ai_next_tank = None
        spawn_at_city(worst if threatened else random.choice(blue_cities), cls)


def ai_attack():
    ai_spend()
    if AI_SPAM:
        if game_time >= AI_START_DELAY:
            ai_spam()
        return
    alive = set(active_units)
    blues = [u for u in active_units if u.team == 'blue']
    for sq in list(ai_squads):
        sq.units = [u for u in sq.units if u in alive and u.ai_squad is sq]
        if sq.finished():
            sq.release()
            ai_squads.remove(sq)
    ai_retreats(blues)
    blue_cities = [c for c in cities if c.team == 'blue']
    for u in blues:
        if u.ai_role == 'garrison' and (u.ai_city is None or u.ai_city.team != 'blue'):
            u.ai_role = None
            u.ai_city = None
    pool = [u for u in blues if u.ai_role is None and game_time >= u.ai_lock]
    ai_garrisons(blue_cities, blues, pool)
    for sq in list(ai_squads):
        sq.update(alive)
    ai_plan_attack(pool)


def draw_zoom_buttons():
    for rect, label in ((ZOOM_IN_RECT, "+"), (ZOOM_OUT_RECT, "-"), (ROTATE_RECT, "R")):
        pygame.draw.rect(screen, (50, 50, 60), rect, border_radius=10)
        pygame.draw.rect(screen, WHITE, rect, 2, border_radius=10)
        t = FONT.render(label, True, WHITE)
        screen.blit(t, t.get_rect(center=rect.center))


def draw_points():
    # small counter at the top centre: your points and how fast they grow
    owned = sum(c.level for c in cities if c.team == 'red')
    rect = pygame.Rect(0, 0, 290, 60)
    rect.center = (SCREEN_WIDTH // 2, 70)
    pygame.draw.rect(screen, (50, 50, 60), rect, border_radius=10)
    pygame.draw.rect(screen, WHITE, rect, 2, border_radius=10)
    draw_text("Points  %d    +%d" % (points, owned * POINTS_PER_CITY),
              FONT_SMALL, WHITE, (rect.centerx, rect.centery - 6))
    # thin bar along the bottom: fills up until the next payout
    frac = min(1.0, point_timer / POINT_INTERVAL)
    bar = pygame.Rect(rect.x + 12, rect.bottom - 12, rect.w - 24, 5)
    pygame.draw.rect(screen, (30, 30, 38), bar, border_radius=3)
    pygame.draw.rect(screen, (90, 170, 255),
                     pygame.Rect(bar.x, bar.y, int(bar.w * frac), bar.h), border_radius=3)


def city_panel_rects():
    # bottom-centre panel: [Spawn Infantry] [Spawn Tank]   [Upgrade + level]
    pw = min(SCREEN_WIDTH - 40, 640)
    ph = 90
    panel = pygame.Rect(0, 0, pw, ph)
    panel.center = (SCREEN_WIDTH // 2, SCREEN_HEIGHT - ph // 2 - 16)
    pad, gap, sep = 10, 8, 18
    bh = ph - 2 * pad
    up_w = int(pw * 0.32)
    sp_w = (pw - 2 * pad - up_w - sep - gap) // 2
    infantry = pygame.Rect(panel.x + pad, panel.y + pad, sp_w, bh)
    tank = pygame.Rect(infantry.right + gap, panel.y + pad, sp_w, bh)
    upgrade = pygame.Rect(panel.right - pad - up_w, panel.y + pad, up_w, bh)
    return panel, infantry, tank, upgrade


def draw_city_panel():
    # buttons cost points and grey out when you can't afford them;
    # the upgrade button shows the city's level and the price of the next one
    c = selected_city
    if c is None:
        return
    panel, infantry, tank, upgrade = city_panel_rects()
    pygame.draw.rect(screen, (30, 30, 40), panel, border_radius=12)
    pygame.draw.rect(screen, WHITE, panel, 2, border_radius=12)
    maxed = c.level >= MAX_LEVEL
    up_cost = 0 if maxed else UPGRADE_COSTS[c.level + 1]
    for rect, top, bottom, fill, cost in (
            (infantry, "Spawn Infantry", "%d pts" % INFANTRY_COST, (40, 60, 100), INFANTRY_COST),
            (tank, "Spawn Tank", "%d pts" % TANK_COST, (40, 60, 100), TANK_COST),
            (upgrade, "Upgrade  Lv %d" % c.level, "MAX" if maxed else "%d pts" % up_cost,
             (90, 70, 30), 10 ** 9 if maxed else up_cost)):
        ok = points >= cost
        pygame.draw.rect(screen, fill if ok else (55, 55, 62), rect, border_radius=10)
        pygame.draw.rect(screen, WHITE if ok else (120, 120, 128), rect, 2, border_radius=10)
        draw_text(top, FONT_TINY, (210, 210, 220) if ok else (140, 140, 148),
                  (rect.centerx, rect.centery - 15))
        draw_text(bottom, FONT_SMALL, WHITE if ok else (140, 140, 148),
                  (rect.centerx, rect.centery + 15))


def draw_selection():
    # a bright ring around the selected dot / city
    c = selected_city
    if c is not None and on_screen(c.rect.centerx, c.rect.centery, 100):
        cx, cy = w2s(c.rect.centerx, c.rect.centery)
        size = max(4, int(60 * zoom)) + 14
        r = pygame.Rect(0, 0, size, size)
        r.center = (int(cx), int(cy))
        pygame.draw.rect(screen, SELECT_COLOR, r, 3, border_radius=max(2, int(10 * zoom)))
    u = selected_unit
    if u is None or u not in active_units or not on_screen(u.x, u.y):
        return
    sx, sy = w2s(u.x, u.y)
    rad = max(3, int(u.radius * zoom))
    pygame.draw.circle(screen, SELECT_COLOR, (int(sx), int(sy)), rad + 7, 3)


# --- Screens: main menu, playing, win / lose ---
state = 'menu'            # 'menu' | 'playing' | 'over'
game_time = 0.0
result_info = {}
dim_surf = None


def draw_dim(alpha=185):
    global dim_surf
    if dim_surf is None or dim_surf.get_size() != (SCREEN_WIDTH, SCREEN_HEIGHT):
        dim_surf = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)
    dim_surf.fill((0, 0, 0, alpha))
    screen.blit(dim_surf, (0, 0))


def draw_text(text, font, color, center):
    img = font.render(text, True, color)
    screen.blit(img, img.get_rect(center=center))


def draw_button(rect, label, fill):
    pygame.draw.rect(screen, fill, rect, border_radius=16)
    pygame.draw.rect(screen, WHITE, rect, 3, border_radius=16)
    draw_text(label, FONT_MID, WHITE, rect.center)


def menu_rects():
    play = pygame.Rect(0, 0, 360, 90)
    play.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.50))
    settings = pygame.Rect(0, 0, 360, 90)
    settings.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.50) + 104)
    return play, settings


def result_rects():
    back = pygame.Rect(0, 0, 360, 80)
    back.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.58))
    return back


def draw_menu():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    draw_text("WORLD WAR", FONT_BIG, RED, (cx, int(SCREEN_HEIGHT * 0.14)))
    draw_text("DOTS", FONT_BIG, BLUE, (cx, int(SCREEN_HEIGHT * 0.14) + 84))
    play, settings = menu_rects()
    draw_button(play, "PLAY", (30, 140, 70))
    draw_button(settings, "SETTINGS", (60, 60, 80))
    draw_menu_tip(cx)


# one tip at a time: shown for 10 s, fades out, 1 s of nothing, then the next one
MENU_TIPS = ("Tap a red dot, then drag to send it",
             "Drag empty ground to move around the map",
             "Pinch or +/- to zoom, R turns the map",
             "Tap your city to spawn units and upgrade it",
             "Cities earn points. Higher level, more points")
TIP_SHOW = 10000          # ms a tip stays up
TIP_GAP = 1000            # ms of blank before the next tip
TIP_FADE = 300            # ms fade in / out
tip_index = 0
tip_start = 0
tip_last_draw = -10 ** 9


def draw_menu_tip(cx):
    global tip_index, tip_start, tip_last_draw
    now = pygame.time.get_ticks()
    if now - tip_last_draw > 500:            # menu just opened: start the cycle fresh
        tip_start = now
    tip_last_draw = now
    cycle = TIP_SHOW + TIP_GAP
    while now - tip_start >= cycle:
        tip_start += cycle
        tip_index = (tip_index + 1) % len(MENU_TIPS)
    t = now - tip_start
    if t >= TIP_SHOW:
        return                               # the 1 s gap
    alpha = min(1.0, t / TIP_FADE, (TIP_SHOW - t) / TIP_FADE)
    y = int(SCREEN_HEIGHT * 0.79)
    items = [("TIP", FONT_TINY, (130, 130, 140), y - 40)]
    for i, part in enumerate(wrap_text(MENU_TIPS[tip_index], FONT_SMALL, SCREEN_WIDTH - 80)):
        items.append((part, FONT_SMALL, (210, 210, 210), y + i * 34))
    for text, font, color, ty in items:
        img = font.render(text, True, color)
        img.set_alpha(int(255 * max(0.0, alpha)))
        screen.blit(img, img.get_rect(center=(cx, ty)))


# --- Settings ---
grid_on = False            # draw a grid over the map
sens = 1.0                 # camera drag / pinch sensitivity (0.5 - 2.0)
slider_drag = None         # None | sens | vol
GRID_STEP = 120            # world pixels between grid lines
SENS_MIN, SENS_MAX = 0.5, 2.0


MUSIC_FILE = "ThemeA_110bpm_FullMix_Loop_ogg.ogg"   # keep this file next to the script
MUSIC_CREDIT = "Music: Sound by Dawn Sound Lab"
music_on = True
music_vol = 0.50           # default volume 50%
music_ok = False


def init_music():
    global music_ok
    try:
        pygame.mixer.init()
        try:
            base = os.path.dirname(os.path.abspath(__file__))
        except NameError:
            base = os.getcwd()
        path = os.path.join(base, MUSIC_FILE)
        if not os.path.exists(path):
            path = MUSIC_FILE
        pygame.mixer.music.load(path)
        pygame.mixer.music.set_volume(music_vol)
        try:
            pygame.mixer.music.play(-1, 0.0, 2000)     # loop forever, 2 s fade-in
        except TypeError:
            pygame.mixer.music.play(-1)
        music_ok = True
    except Exception:
        music_ok = False                                # no file / no audio: stay silent


def apply_music():
    if not music_ok:
        return
    try:
        pygame.mixer.music.set_volume(music_vol)
        if music_on:
            pygame.mixer.music.unpause()
        else:
            pygame.mixer.music.pause()
    except Exception:
        pass


def settings_rects():
    cx = SCREEN_WIDTH // 2
    H = SCREEN_HEIGHT
    r = {}
    r['grid'] = pygame.Rect(0, 0, 150, 64)
    r['grid'].center = (cx + 130, int(H * 0.27))
    r['music'] = pygame.Rect(0, 0, 150, 64)
    r['music'].center = (cx + 130, int(H * 0.40))
    r['sens'] = pygame.Rect(0, 0, 480, 14)
    r['sens'].center = (cx, int(H * 0.57))
    r['vol'] = pygame.Rect(0, 0, 480, 14)
    r['vol'].center = (cx, int(H * 0.72))
    r['back'] = pygame.Rect(0, 0, 260, 70)
    r['back'].center = (cx, int(H * 0.86))
    return r


def set_slider_from_x(which, x):
    global sens, music_vol
    track = settings_rects()[which]
    frac = max(0.0, min(1.0, (x - track.x) / track.w))
    if which == 'sens':
        sens = SENS_MIN + (SENS_MAX - SENS_MIN) * frac
    else:
        music_vol = frac
        apply_music()


def draw_slider(track, frac):
    pygame.draw.rect(screen, (70, 70, 90), track, border_radius=7)
    fill = pygame.Rect(track.x, track.y, int(track.w * frac), track.h)
    pygame.draw.rect(screen, (90, 170, 255), fill, border_radius=7)
    pygame.draw.circle(screen, WHITE, (track.x + int(track.w * frac), track.centery), 22)


def draw_settings():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    r = settings_rects()
    draw_text("SETTINGS", FONT_BIG, WHITE, (cx, int(SCREEN_HEIGHT * 0.12)))
    draw_text("Grid", FONT_MID, WHITE, (cx - 130, r['grid'].centery))
    draw_button(r['grid'], "YES" if grid_on else "NO",
                (30, 140, 70) if grid_on else (110, 50, 50))
    draw_text("Music", FONT_MID, WHITE, (cx - 130, r['music'].centery))
    draw_button(r['music'], "ON" if music_on else "OFF",
                (30, 140, 70) if music_on else (110, 50, 50))
    draw_text("Sensitivity   %.1fx" % sens, FONT_MID, WHITE,
              (cx, r['sens'].centery - 46))
    draw_slider(r['sens'], (sens - SENS_MIN) / (SENS_MAX - SENS_MIN))
    draw_text("Volume   %d%%" % int(round(music_vol * 100)), FONT_MID, WHITE,
              (cx, r['vol'].centery - 46))
    draw_slider(r['vol'], music_vol)
    draw_button(r['back'], "BACK", (60, 60, 80))
    draw_text(MUSIC_CREDIT, FONT_SMALL, (150, 150, 160),
              (cx, int(SCREEN_HEIGHT * 0.96)))


def draw_grid():
    # Thin grid over the whole map (lines follow the camera and rotation).
    color = (75, 135, 90)
    for x in range(0, WORLD_W + 1, GRID_STEP):
        pygame.draw.line(screen, color, w2s(x, 0), w2s(x, WORLD_H), 1)
    for y in range(0, WORLD_H + 1, GRID_STEP):
        pygame.draw.line(screen, color, w2s(0, y), w2s(WORLD_W, y), 1)


settings_from = 'menu'      # where the Settings screen's BACK button returns to


def draw_pause_button():
    pygame.draw.rect(screen, (50, 50, 60), PAUSE_RECT, border_radius=10)
    pygame.draw.rect(screen, WHITE, PAUSE_RECT, 2, border_radius=10)
    bx, by = PAUSE_RECT.center
    pygame.draw.rect(screen, WHITE, (bx - 12, by - 14, 9, 28))
    pygame.draw.rect(screen, WHITE, (bx + 3, by - 14, 9, 28))


def pause_rects():
    rects = []
    for i in range(3):
        r = pygame.Rect(0, 0, 360, 84)
        r.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.38) + i * 100)
        rects.append(r)
    return rects          # resume, settings, exit


def draw_pause():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    draw_text("PAUSED", FONT_BIG, WHITE, (cx, int(SCREEN_HEIGHT * 0.17)))
    resume, settings, exit_btn = pause_rects()
    draw_button(resume, "RESUME", (30, 140, 70))
    draw_button(settings, "SETTINGS", (60, 60, 80))
    draw_button(exit_btn, "EXIT", (140, 50, 50))


def pause_game():
    global state, dragging_unit, drag_points, panning, pinching, pinch_last
    state = 'paused'
    dragging_unit = None
    drag_points = []
    panning = False
    fingers.clear()
    pinching = False
    pinch_last = None


# --- Loading screen shown before a match ---
LOADING_LINES = ("The World War has started.",
                 "The enemy nation has attacked us.",
                 "Prepare for war, Commander.")
# long enough for an average reader (~3.5 words a second) plus a moment to settle
LOADING_MS = int(sum(len(l.split()) for l in LOADING_LINES) / 3.5 * 1000 + 1000)
loading_frames = 0
loading_start = 0


def wrap_text(text, font, max_w):
    lines, cur = [], ""
    for w in text.split():
        test = (cur + " " + w).strip()
        if font.size(test)[0] <= max_w or not cur:
            cur = test
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines


def draw_loading():
    screen.fill(BG_COLOR)
    cx = SCREEN_WIDTH // 2
    y = int(SCREEN_HEIGHT * 0.30)
    for i, line in enumerate(LOADING_LINES):
        for part in wrap_text(line, FONT_MID, SCREEN_WIDTH - 120):
            draw_text(part, FONT_MID, RED if i == 0 else WHITE, (cx, y))
            y += 62
        y += 14
    draw_text("Map: " + MAPS[selected_map][0] + "   -   " + difficulty.upper(), FONT_SMALL, (150, 150, 160), (cx, y + 6))
    bar = pygame.Rect(0, 0, 520, 12)
    bar.center = (cx, int(SCREEN_HEIGHT * 0.86))
    if loading_frames > 2:
        frac = min(1.0, (pygame.time.get_ticks() - loading_start) / LOADING_MS)
    else:
        frac = 0.0
    pygame.draw.rect(screen, (60, 60, 70), bar, border_radius=6)
    pygame.draw.rect(screen, (90, 170, 255),
                     pygame.Rect(bar.x, bar.y, int(bar.w * frac), bar.h), border_radius=6)
    draw_text("Loading...", FONT_SMALL, (150, 150, 160), (cx, bar.y - 30))


def draw_result():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    won = result_info.get('result') == 'win'
    draw_text("VICTORY" if won else "DEFEAT", FONT_BIG,
              GREEN if won else RED, (cx, int(SCREEN_HEIGHT * 0.2)))
    t = int(result_info.get('time', 0))
    draw_text("Time  %d:%02d" % (t // 60, t % 60), FONT_SMALL, WHITE,
              (cx, int(SCREEN_HEIGHT * 0.34)))
    draw_text("Your cities %d    Enemy cities %d" % (result_info.get('red', 0),
                                                   result_info.get('blue', 0)),
              FONT_SMALL, WHITE, (cx, int(SCREEN_HEIGHT * 0.34) + 38))
    draw_button(result_rects(), "BACK", (60, 60, 80))


# --- Maps ---
MAPS = [
    ("FRONTIER", "Open fields. No terrain.", 'open'),
    ("RIVER CROSSING", "A wide river with three bridges.", 'rivers'),
    ("HIGHLANDS", "A mountain wall with narrow passes.", 'highlands'),
    ("TWIN RIVERS", "Two rivers with few crossings.", 'twin'),
]
selected_map = 0
map_bridges = []           # crossing points (bridges / passes) the AI can route through
terrain_cells = []         # indices of all cells that have terrain


def add_river(base_y, amp, freq, phase, half, bridges, bridge_half=60):
    for gx in range(GW):
        x = gx * CELL + CELL / 2
        on_bridge = any(abs(x - bx) < bridge_half for bx in bridges)
        yc = base_y + amp * math.sin(x * freq + phase)
        for gy in range(max(0, int((yc - half) // CELL)), min(GH, int((yc + half) // CELL) + 1)):
            TERRAIN[gy * GW + gx] = BRIDGE if on_bridge else RIVER
    for bx in bridges:
        map_bridges.append((bx, base_y + amp * math.sin(bx * freq + phase)))


def add_blob(cx, cy, r, code, only_empty=False):
    for gy in range(max(0, int((cy - r) // CELL)), min(GH, int((cy + r) // CELL) + 1)):
        for gx in range(max(0, int((cx - r) // CELL)), min(GW, int((cx + r) // CELL) + 1)):
            if (gx * CELL + CELL / 2 - cx) ** 2 + (gy * CELL + CELL / 2 - cy) ** 2 <= r * r:
                if not only_empty or TERRAIN[gy * GW + gx] == 0:
                    TERRAIN[gy * GW + gx] = code


def add_forests(per_side=6):
    """Natural-looking woods: each grove is a cluster of overlapping blobs of
    different sizes. Same number on both sides; rivers and mountains stay clear."""
    mid = WORLD_H / 2
    for lo, hi in ((150, mid - 120), (mid + 120, WORLD_H - 150)):
        placed = []
        for _ in range(per_side * 12):
            if len(placed) >= per_side:
                break
            cx = random.randint(120, WORLD_W - 120)
            cy = random.randint(int(lo), int(hi))
            if terrain_at(cx, cy) != 0 or any(dist(cx, cy, px, py) < 280 for px, py in placed):
                continue
            placed.append((cx, cy))
            r = random.randint(90, 140)
            for _ in range(random.randint(5, 8)):
                ang = random.uniform(0, 2 * math.pi)
                off = random.uniform(0, r * 0.7)
                add_blob(cx + math.cos(ang) * off, cy + math.sin(ang) * off,
                         random.uniform(r * 0.45, r * 0.8), FOREST, only_empty=True)


def add_mountain(cx, cy, r):
    for gy in range(max(0, int((cy - r) // CELL)), min(GH, int((cy + r) // CELL) + 1)):
        for gx in range(max(0, int((cx - r) // CELL)), min(GW, int((cx + r) // CELL) + 1)):
            if (gx * CELL + CELL / 2 - cx) ** 2 + (gy * CELL + CELL / 2 - cy) ** 2 <= r * r:
                TERRAIN[gy * GW + gx] = MOUNTAIN


def build_terrain(kind):
    TERRAIN[:] = bytes(len(TERRAIN))
    map_bridges.clear()
    mid = WORLD_H / 2
    if kind == 'rivers':
        add_river(mid, 40, 0.006, 0.0, 55, [300, 720, 1140])
    elif kind == 'highlands':
        passes = (250, 720, 1190)
        PASS_HALF = 85                       # half the width of each pass
        # the wall is split into stretches between the passes; each stretch is
        # filled with a thick band of big, uneven mountains (3 rows deep), and
        # the outer blobs are pushed flush against the pass edges
        stretches = [(-200, passes[0] - PASS_HALF)]
        for a, b in zip(passes, passes[1:]):
            stretches.append((a + PASS_HALF, b - PASS_HALF))
        stretches.append((passes[-1] + PASS_HALF, WORLD_W + 200))
        for lo, hi in stretches:
            for row_dy in (-105, 0, 105):
                x = lo
                while x < hi + 60:
                    r = random.randint(115, 150)
                    if hi - lo < 2 * r:
                        r = max(40, (hi - lo) // 2)
                    cx = max(lo + r, min(hi - r, x + random.randint(-15, 15)))
                    cy = mid + 30 * math.sin(cx * 0.01) + row_dy + random.randint(-25, 25)
                    add_mountain(cx, cy, r)
                    x += 85
        for p in passes:
            map_bridges.append((p, mid))
        for cx, cy in ((200, mid - 430), (1240, mid + 430), (720, mid - 520), (720, mid + 520)):
            add_mountain(cx, cy, 120)
    elif kind == 'twin':
        add_river(mid - 300, 30, 0.007, 1.0, 45, [450, 990])
        add_river(mid + 300, 30, 0.007, 3.0, 45, [240, 720, 1200])
        add_mountain(150, mid, 100)
        add_mountain(1290, mid, 100)
    add_forests()                       # woods on every map
    terrain_cells[:] = [i for i, t in enumerate(TERRAIN) if t]


def mapselect_rects():
    rects = []
    for i in range(len(MAPS)):
        r = pygame.Rect(0, 0, 560, 96)
        r.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.29) + i * 106)
        rects.append(r)
    back = pygame.Rect(0, 0, 240, 64)
    back.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.92))
    return rects, back


def draw_mapselect():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    draw_text("SELECT MAP", FONT_BIG, WHITE, (cx, int(SCREEN_HEIGHT * 0.12)))
    rects, back = mapselect_rects()
    for (name, desc, _), r in zip(MAPS, rects):
        pygame.draw.rect(screen, (40, 50, 70), r, border_radius=16)
        pygame.draw.rect(screen, WHITE, r, 3, border_radius=16)
        draw_text(name, FONT_MID, WHITE, (r.centerx, r.centery - 18))
        draw_text(desc, FONT_SMALL, (190, 190, 200), (r.centerx, r.centery + 24))
    draw_button(back, "BACK", (60, 60, 80))


# --- Difficulty ---
DIFFICULTIES = {
    'easy': dict(think=1.5, delay=20.0, spam=True, per_tick=2,
                 upgrade_budget=0, tank_share=0.0, save_min=None),
    'medium': dict(think=2.5, delay=50.0, spam=False, ratio=1.15, squad_min=5,
                   squad_max=12, max_squads=2, interceptors=1, retreat=0.2,
                   cooldown=20.0, two_prong=False, tact_open=(2, 3, 5),
                   tact_contested=(3, 7), garrison=2,
                   upgrade_budget=3, tank_share=0.25, save_min=25),
    'hard': dict(think=2.0, delay=60.0, spam=False, ratio=1.6, squad_min=6,
                 squad_max=16, max_squads=3, interceptors=3, retreat=0.4,
                 cooldown=40.0, two_prong=True, tact_open=(6, 3, 1),
                 tact_contested=(7, 3), garrison=4,
                 upgrade_budget=6, tank_share=0.4, save_min=15),
}
DIFFICULTY_INFO = [
    ('easy', "EASY", "Not very smart. Attacks fast and spams units."),
    ('medium', "MEDIUM", "Squads and tactics, a bit forgiving."),
    ('hard', "HARD", "Patient. Rare, strong, coordinated attacks."),
]
difficulty = 'medium'      # default


def apply_difficulty():
    global AI_SPAWN_INTERVAL, AI_START_DELAY, AI_SPAM, AI_DOTS_PER_TICK
    global ATTACK_RATIO, SQUAD_MIN, SQUAD_MAX, MAX_SQUADS, MAX_INTERCEPTORS
    global RETREAT_HP, ATTACK_COOLDOWN, TWO_PRONG, TACT_OPEN, TACT_CONTESTED, GARRISON_CAP
    global AI_UPGRADE_BUDGET, AI_TANK_SHARE, AI_SAVE_MIN_UNITS
    d = DIFFICULTIES[difficulty]
    AI_SPAWN_INTERVAL = d['think']
    AI_START_DELAY = d['delay']
    AI_SPAM = d['spam']
    AI_UPGRADE_BUDGET = d['upgrade_budget']
    AI_TANK_SHARE = d['tank_share']
    AI_SAVE_MIN_UNITS = d['save_min']
    if AI_SPAM:
        AI_DOTS_PER_TICK = d['per_tick']
        return
    ATTACK_RATIO = d['ratio']
    SQUAD_MIN = d['squad_min']
    SQUAD_MAX = d['squad_max']
    MAX_SQUADS = d['max_squads']
    MAX_INTERCEPTORS = d['interceptors']
    RETREAT_HP = d['retreat']
    ATTACK_COOLDOWN = d['cooldown']
    TWO_PRONG = d['two_prong']
    TACT_OPEN = d['tact_open']
    TACT_CONTESTED = d['tact_contested']
    GARRISON_CAP = d['garrison']


def difficulty_rects():
    rects = []
    for i in range(len(DIFFICULTY_INFO)):
        r = pygame.Rect(0, 0, 600, 96)
        r.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.32) + i * 106)
        rects.append(r)
    back = pygame.Rect(0, 0, 240, 64)
    back.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.92))
    return rects, back


def draw_difficulty():
    draw_dim()
    cx = SCREEN_WIDTH // 2
    draw_text("DIFFICULTY", FONT_BIG, WHITE, (cx, int(SCREEN_HEIGHT * 0.12)))
    rects, back = difficulty_rects()
    for (key, name, desc), r in zip(DIFFICULTY_INFO, rects):
        pygame.draw.rect(screen, (40, 50, 70), r, border_radius=16)
        chosen = key == difficulty
        pygame.draw.rect(screen, GREEN if chosen else WHITE, r, 6 if chosen else 3,
                         border_radius=16)
        draw_text(name, FONT_MID, WHITE, (r.centerx, r.centery - 18))
        draw_text(desc, FONT_SMALL, (190, 190, 200), (r.centerx, r.centery + 24))
    draw_button(back, "BACK", (60, 60, 80))


def reset_game():
    global game_time, ai_timer, land_timer, dirty_box, terr_cache
    global zoom, cam_cx, cam_cy, dragging_unit, drag_points, panning
    global pinching, pinch_last, selected_unit, points, point_timer, selected_city, ai_points, ai_next_tank
    global last_attack_time
    apply_difficulty()
    last_attack_time = -1e9
    build_terrain(MAPS[selected_map][2])
    cities[:] = (scatter(CITY_COLS, CITY_ROWS, 100, int(STARTING_MID_Y) - 300, 'blue')
                 + scatter(CITY_COLS, CITY_ROWS, int(STARTING_MID_Y) + 240, WORLD_H - 100, 'red'))
    for row in owner:
        row[:] = [OWN_BLUE] * GW
    terr.fill(TERR_COLORS[OWN_BLUE])
    edge_surf.fill(EDGE_OFF)
    rows = []
    for gx in range(GW):
        by = STARTING_MID_Y + 12 * math.sin(gx * CELL * 0.012)
        yb = max(0, min(GH, int((by - CELL / 2) // CELL) + 1))
        rows.append(yb)
        for gy in range(yb, GH):
            owner[gy][gx] = OWN_RED
        terr.fill(TERR_COLORS[OWN_RED], (gx, yb, 1, GH - yb))
    for gx in range(GW):
        yb = rows[gx]
        for gy in range(max(0, yb - 3), min(GH, yb + 3)):
            refresh_cell(gx, gy)
    for idx in terrain_cells:
        refresh_cell(idx % GW, idx // GW)
    active_units.clear()
    ai_squads.clear()
    for i in range(START_DOTS):
        sx = 72 + i * (WORLD_W - 144) / (START_DOTS - 1)
        active_units.append(Infantry(sx, STARTING_MID_Y + 70, 'red'))
        active_units.append(Infantry(sx, STARTING_MID_Y - 70, 'blue'))
    for i in range(START_TANKS):
        tx = 200 + i * (WORLD_W - 400) / (START_TANKS - 1)
        active_units.append(Tank(tx, STARTING_MID_Y + 130, 'red'))
        active_units.append(Tank(tx, STARTING_MID_Y - 130, 'blue'))
    pending_seeds.clear()
    smooth_chunks.clear()
    dirty_box = None
    terr_cache = None
    zoom = 0.7
    cam_cx = WORLD_W / 2
    cam_cy = WORLD_H * 0.62
    clamp_camera()
    game_time = 0.0
    points = 0
    ai_points = 0
    ai_next_tank = None
    point_timer = 0.0
    ai_timer = 0.0
    land_timer = 0.0
    dragging_unit = None
    selected_unit = None
    selected_city = None
    drag_points = []
    panning = False
    fingers.clear()
    pinching = False
    pinch_last = None


def end_game(kind, red_n, blue_n):
    global state, dragging_unit, drag_points, panning, pinching, pinch_last, selected_unit
    global selected_city
    state = 'over'
    result_info.update(result=kind, time=game_time, red=red_n, blue=blue_n)
    dragging_unit = None
    selected_unit = None
    selected_city = None
    drag_points = []
    panning = False
    fingers.clear()
    pinching = False
    pinch_last = None


def ui_click(pos):
    global state, grid_on, slider_drag, settings_from, music_on, loading_frames, selected_map, difficulty
    if state == 'menu':
        play, settings = menu_rects()
        if play.collidepoint(pos):
            state = 'mapselect'
        elif settings.collidepoint(pos):
            settings_from = 'menu'
            state = 'settings'
    elif state == 'paused':
        resume, settings, exit_btn = pause_rects()
        if resume.collidepoint(pos):
            state = 'playing'
        elif settings.collidepoint(pos):
            settings_from = 'paused'
            state = 'settings'
        elif exit_btn.collidepoint(pos):
            state = 'menu'          # match is dropped (saving comes later)
    elif state == 'mapselect':
        rects, back = mapselect_rects()
        for i, rr in enumerate(rects):
            if rr.collidepoint(pos):
                selected_map = i
                state = 'difficulty'
                break
        else:
            if back.collidepoint(pos):
                state = 'menu'
    elif state == 'difficulty':
        rects, back = difficulty_rects()
        for (key, _, _), rr in zip(DIFFICULTY_INFO, rects):
            if rr.collidepoint(pos):
                difficulty = key
                state = 'loading'      # the match is built while the loading screen shows
                loading_frames = 0
                break
        else:
            if back.collidepoint(pos):
                state = 'mapselect'
    elif state == 'settings':
        r = settings_rects()
        if r['grid'].collidepoint(pos):
            grid_on = not grid_on
        elif r['music'].collidepoint(pos):
            music_on = not music_on
            apply_music()
        elif r['back'].collidepoint(pos):
            state = 'playing' if settings_from == 'paused' else settings_from
            slider_drag = None
        elif r['sens'].inflate(40, 70).collidepoint(pos):
            slider_drag = 'sens'
            set_slider_from_x('sens', pos[0])
        elif r['vol'].inflate(40, 70).collidepoint(pos):
            slider_drag = 'vol'
            set_slider_from_x('vol', pos[0])
    elif state == 'over':
        if result_rects().collidepoint(pos):
            state = 'menu'


init_music()

HAS_FINGERS = hasattr(pygame, "FINGERDOWN")
RESIZE2 = getattr(pygame, "WINDOWRESIZED", None)

while True:
    dt = min(clock.tick(60) / 1000.0, 0.05)
    screen.fill(BG_COLOR)

    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            pygame.quit()
            sys.exit()

        if event.type == pygame.VIDEORESIZE:
            on_window_resize(event.w, event.h)
        elif RESIZE2 is not None and event.type == RESIZE2:
            on_window_resize(event.x, event.y)

        if state != 'playing':
            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                ui_click(event.pos)
            elif event.type == pygame.MOUSEMOTION and slider_drag:
                set_slider_from_x(slider_drag, event.pos[0])
            elif event.type == pygame.MOUSEBUTTONUP:
                slider_drag = None
            continue

        # --- Pinch zoom (two fingers) ---
        if HAS_FINGERS and event.type == pygame.FINGERDOWN:
            fingers[event.finger_id] = (event.x * SCREEN_WIDTH, event.y * SCREEN_HEIGHT)
            if len(fingers) >= 2:
                pinching = True
                dragging_unit = None
                drag_points = []
                panning = False
                a, b = list(fingers.values())[:2]
                pinch_last = dist(a[0], a[1], b[0], b[1])
            continue
        if HAS_FINGERS and event.type == pygame.FINGERMOTION:
            fingers[event.finger_id] = (event.x * SCREEN_WIDTH, event.y * SCREEN_HEIGHT)
            if pinching and len(fingers) >= 2:
                a, b = list(fingers.values())[:2]
                d = dist(a[0], a[1], b[0], b[1])
                if pinch_last and pinch_last > 1:
                    set_zoom(zoom * (d / pinch_last) ** sens, (a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
                pinch_last = d
            continue
        if HAS_FINGERS and event.type == pygame.FINGERUP:
            fingers.pop(event.finger_id, None)
            if len(fingers) < 2:
                pinch_last = None
            if not fingers:
                pinching = False
            continue

        if pinching:
            continue

        # --- Touch / mouse ---
        if event.type == pygame.MOUSEBUTTONDOWN:
            if event.button in (4, 5):   # mouse wheel (desktop testing)
                set_zoom(zoom * (ZOOM_STEP if event.button == 4 else 1 / ZOOM_STEP),
                         event.pos[0], event.pos[1])
            elif PAUSE_RECT.collidepoint(event.pos):
                pause_game()
            elif ZOOM_IN_RECT.collidepoint(event.pos):
                set_zoom(zoom * ZOOM_STEP, SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2)
            elif ZOOM_OUT_RECT.collidepoint(event.pos):
                set_zoom(zoom / ZOOM_STEP, SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2)
            elif ROTATE_RECT.collidepoint(event.pos):
                rotate_view()
            elif selected_city is not None and city_panel_rects()[0].collidepoint(event.pos):
                _, b_inf, b_tank, _b_up = city_panel_rects()
                if b_inf.collidepoint(event.pos):
                    buy_unit(selected_city, Infantry, INFANTRY_COST)
                elif b_tank.collidepoint(event.pos):
                    buy_unit(selected_city, Tank, TANK_COST)
                elif _b_up.collidepoint(event.pos) and selected_city.level < MAX_LEVEL:
                    up_cost = UPGRADE_COSTS[selected_city.level + 1]
                    if points >= up_cost:
                        points -= up_cost
                        selected_city.level += 1
            else:
                wx, wy = s2w(*event.pos)
                grab = None
                best = TOUCH_GRAB / zoom
                for u in active_units:
                    d = dist(u.x, u.y, wx, wy)
                    if u.team == 'red' and d <= best:
                        grab, best = u, d
                if grab:
                    if grab is selected_unit:
                        # already selected: this drag draws its path
                        dragging_unit = grab
                        drag_points = [(grab.x, grab.y)]
                    else:
                        # first tap just selects it; no path without selecting
                        selected_unit = grab
                        selected_city = None
                else:
                    # empty ground or one of your cities: a drag pans, a tap selects
                    tap_city = None
                    for c in cities:
                        if c.team == 'red' and c.rect.inflate(30, 30).collidepoint(wx, wy):
                            tap_city = c
                            break
                    panning = True
                    pan_last = event.pos
                    pan_start = event.pos
                    pan_moved = False

        elif event.type == pygame.MOUSEMOTION:
            if dragging_unit:
                wx, wy = s2w(*event.pos)
                px, py = clamp_x(wx), clamp_y(wy)
                lx, ly = drag_points[-1]
                if dist(lx, ly, px, py) >= PATH_POINT_SPACING / zoom:
                    drag_points.append((px, py))
            elif panning:
                if dist(event.pos[0], event.pos[1], pan_start[0], pan_start[1]) > TAP_SLOP:
                    pan_moved = True
                pdx, pdy = unrot_vec((event.pos[0] - pan_last[0]) * sens / zoom,
                                     (event.pos[1] - pan_last[1]) * sens / zoom)
                cam_cx -= pdx
                cam_cy -= pdy
                pan_last = event.pos
                clamp_camera()

        elif event.type == pygame.MOUSEBUTTONUP:
            if dragging_unit and len(drag_points) > 1 and dragging_unit in active_units:
                dragging_unit.path = list(drag_points[1:])
                dragging_unit.retreating = dragging_unit.in_combat
            if panning and not pan_moved:
                selected_unit = None      # tapped ground: drop the dot selection
                selected_city = tap_city  # a tapped red city opens its panel, empty ground closes it
            tap_city = None
            dragging_unit = None
            drag_points = []
            panning = False

    # --- UPDATE ---
    if state == 'loading':
        loading_frames += 1
        if loading_frames == 2:                 # first frame has been shown; build the match
            reset_game()
            loading_start = pygame.time.get_ticks()
        elif loading_frames > 2 and pygame.time.get_ticks() - loading_start >= LOADING_MS:
            state = 'playing'
    if state == 'playing':
        game_time += dt
        ai_timer += dt
        if ai_timer >= AI_SPAWN_INTERVAL:
            ai_timer = 0.0
            ai_attack()

        for u in active_units:
            u.update_move(dt)
        update_combat(active_units, dt)
        if selected_unit is not None and selected_unit not in active_units:
            selected_unit = None              # it died
        if selected_city is not None and selected_city.team != 'red':
            selected_city = None              # city was captured
        update_healing(active_units, dt)
        for u in active_units:
            if paint_dot(u):
                terr_dirty = True
        land_timer += dt
        if land_timer >= 0.35:
            land_timer = 0.0
            tidy_land()
        update_capture(active_units, dt)

        red_n = sum(1 for c in cities if c.team == 'red')
        point_timer += dt
        if point_timer >= POINT_INTERVAL:
            point_timer -= POINT_INTERVAL
            points += sum(c.level for c in cities if c.team == 'red') * POINTS_PER_CITY
            ai_points += sum(c.level for c in cities if c.team == 'blue') * POINTS_PER_CITY
        blue_n = len(cities) - red_n
        if blue_n == 0:
            end_game('win', red_n, blue_n)
        elif red_n == 0:
            end_game('lose', red_n, blue_n)

    # --- DRAW ---
    if state != 'loading':
        draw_territory()
        if grid_on:
            draw_grid()
        for city in cities:
            city.draw(screen)
        for u in active_units:
            u.draw(screen)
        if state in ('playing', 'paused'):
            draw_selection()

    if state == 'playing':
        if dragging_unit and len(drag_points) > 1:
            pygame.draw.lines(screen, RED, False,
                              [w2s(px, py) for px, py in drag_points], 3)
        draw_zoom_buttons()
        draw_pause_button()
        draw_points()
        draw_city_panel()
    elif state == 'paused':
        draw_pause()
    elif state == 'menu':
        draw_menu()
    elif state == 'settings':
        draw_settings()
    elif state == 'mapselect':
        draw_mapselect()
    elif state == 'difficulty':
        draw_difficulty()
    elif state == 'loading':
        draw_loading()
    else:
        draw_result()
    pygame.display.flip()
