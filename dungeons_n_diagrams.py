from z3 import *
from itertools import *
from dataclasses import dataclass
from collections import defaultdict

@dataclass
class Dungeon:
    col_hints: [int] # Numbers at the top
    row_hints: [int] # Numbers on the left

    # The origin is at the top left, so the top left tile is (0,0)
    monsters: [(int, int)]
    treasures: [(int, int)]

def print_dungeon_solutions(dungeon: Dungeon):
    s = Solver()

    col_hints = dungeon.col_hints
    row_hints = dungeon.row_hints
    width  = len(col_hints)
    height = len(row_hints)
    monsters  = dungeon.monsters
    treasures = dungeon.treasures

    def BoolCount(vs):
        return Count(vs, lambda x: x)

    def Count(vs, pred):
        return Sum([If(pred(v), 1, 0) for v in vs])

    out_of_bounds_wall = Bool('out_of_bounds')
    s.add(out_of_bounds_wall == True)
    wall_map = defaultdict(lambda: defaultdict(lambda: out_of_bounds_wall))

    for (x, y) in product(range(width), range(height)):
        wall_map[x][y] = Bool(f'w_{x}_{y}')

    # Tiles that contain a monster or a treasure chest cannot also be a wall.
    for (x, y) in (monsters + treasures):
        s.add(wall_map[x][y] == False)

    # Not a map to find pirate booty, but a map to store what tiles are part of
    # a treasure room.
    treasure_map = defaultdict(dict)
    for (x, y) in product(range(width), range(height)):
        treasure_map[x][y] = Bool(f't_{x}_{y}') 

    # If there are no treasures, then there cannot be treasure rooms.
    if len(treasures) == 0:
        for (x, y) in product(range(width), range(height)):
            s.add(treasure_map[x][y] == False)

    def range_inc(start, stop):
        return range(start, stop+1)

    def treasure_room_positions(x, y):
        # Given the position of a treasure chest (x,y), return all possible
        # and valid treasure room center positions for this treasure chest.
        res = []

        for (cx, cy) in product(range_inc(x-1,x+1), range_inc(y-1,y+1)):
            # Ensure that the entire treasure room is in bounds.
            if cx <= 0 or cx >= (width-1) or cy <= 0 or cy >= (height-1):
                continue

            res.append((cx,cy))

        return res

    def are_rooms_too_close(a, b):
        # Checks whether two treasure rooms are far enough apart so that they
        # do not overlap and there is enough room for a separating wall.
        # This is achieved by treating one room as having a 5x5 area and the
        # other a 3x3 area and checking if they overlap.
        (x1, y1) = a
        (x2, y2) = b
        return (x2-2) <= (x1+1) and (x2+2) >= (x1-1) and (y2-2) <= (y1+1) and (y2+2) >= (y1-1) 

    treasure_room_constraints = []

    # All possible combinations for different treasure room locations.
    treasure_room_position_combinations = product(*[treasure_room_positions(x, y) for (x,y) in treasures])

    for centers in treasure_room_position_combinations:
        # If any of the treasure rooms are too close to each other, then we
        # know that this treasure room layout configuration is invalid and we
        # skip it.
        if any([are_rooms_too_close(a,b) for (a,b) in combinations(centers,2)]):
            continue

        treasure_room_layout_constraints = []

        # Create a bitmap of which tiles are part of a treasure room
        m = defaultdict(lambda: defaultdict(lambda: False))
        for (x,y) in centers:
            for (tx,ty) in product(range_inc(x-1,x+1), range_inc(y-1,y+1)):
                m[tx][ty] = True

            wall_positions = [
                (x-2, y-1), (x-2, y),   (x-2, y+1),
                (x+2, y-1), (x+2, y),   (x+2, y+1),
                (x-1, y-2), (x,   y-2), (x+1, y-2),
                (x-1, y+2), (x,   y+2), (x+1, y+2),
            ]

            room_walls = [wall_map[x][y] for (x,y) in wall_positions]
            treasure_room_layout_constraints.append(BoolCount(room_walls) == 11)

        for (x,y) in product(range(width), range(height)):
            if m[x][y]:
                treasure_room_layout_constraints.append(wall_map[x][y] == False)

            treasure_room_layout_constraints.append(treasure_map[x][y] == m[x][y])

        treasure_room_constraints.append(And(treasure_room_layout_constraints))

    s.add(Or(treasure_room_constraints))

    def column(grid, x):
        return [grid[x][y] for y in range(height)]

    def row(grid, y):
        return [grid[x][y] for x in range(width)]

    def neighbours(grid, x, y):
        ps = [(x, y-1), (x+1, y), (x, y+1), (x-1, y)]
        return [grid[tx][ty] for (tx, ty) in ps]

    # The number of walls in each column must match the hint.
    for (x, c) in enumerate(col_hints):
        s.add(BoolCount(column(wall_map, x)) == c)

    # The number of walls in each row must match the hint.
    for (y, c) in enumerate(row_hints):
        s.add(BoolCount(row(wall_map, y)) == c)

    # A monster must be in a dead end, meaning it is surrounded by 3 walls.
    for (x, y) in monsters:
        s.add(BoolCount(neighbours(wall_map, x, y)) == 3)

    # Disallow dead ends without monsters
    for (x, y) in product(range(width), range(height)):
        ns = neighbours(wall_map, x, y)
        s.add(If(And(BoolCount(ns) == 3, (x, y) not in monsters),
                 wall_map[x][y],
                 True))

    # Disallow 2x2 empty spaces that are not part of a treasure room.
    for (x, y) in product(range(width), range(height)):
        # If we have an empty tile that is not part of a treasure room, then 
        # one of the three others in this 2x2  window must have a wall.
        s.add(If(And(Not(wall_map[x][y]), Not(treasure_map[x][y])),
                 Or(wall_map[x+1][y], wall_map[x][y+1], wall_map[x+1][y+1]),
                 True))

    # NOTE: There is no constraint that ensures that all empty spaces are connected,
    # but so far the program has only found unique solutions, so adding constraints
    # for this has been unnecessary. Nevertheless, it prints all solutions it can find.

    if s.check() == unsat:
        # Impossible if you give it a dungeon that's in the game, because those # all have a solution.
        print('Impossible. Did you mistype something?')
        return

    solutions = []

    while s.check() == sat:
        m = s.model()
        solutions.append(m)

        # To find another solution, we invalidate the current solution and request a new solution.
        # This is done by saying that at least one of the wall tiles must have
        # a different assignment.
        s.add(Or([wall_map[x][y] != m[wall_map[x][y]] for (x,y) in product(range(width), range(height))]))

    if len(solutions) == 1:
        print('A unique solution was found!')
    else:
        print(f'{len(solutions)} solutions were found!')

    for s in solutions:
        for y in range(height):
            for x in range(width):
                if (x, y) in monsters:
                    print('M', end='')
                elif (x, y) in treasures:
                    print('T', end='')
                else:
                    print('█' if s[wall_map[x][y]] else '░', end='')
            print('')
        print('\n')

if __name__ == '__main__':
    # Second puzzle from the last row
    puz_1_7 = Dungeon(
        [2,4,2,5,2,5,3,5],
        [3,4,3,6,3,1,3,5],
        [(0,2),(5,0),(6,3),(7,4),(7,6)],
        [(2,5)]
    )
    print_dungeon_solutions(puz_1_7)