#!/usr/bin/env python3
"""Write paper/macmahon-cubes.svg: all 30 cubes, opened out, in Conway's tableau.

Faces come from results/cubes/geometry.json and are drawn as in Johnson and
Roldan's Figure 2, in the left-handed frame the paper uses: +x right, +y down,
+z towards the viewer. Stops if any cube disagrees with results/cubes/tableau.txt.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results/cubes'
OUTPUT = ROOT / 'paper/macmahon-cubes.svg'

LABELS = 'ABCDEF'
FACE_COLOURS = {1: '#C8401F', 2: '#F2C230', 3: '#1E8A5A', 4: '#24489C', 5: '#EE9BC4', 6: '#62C4E6'}
FACE_INK = {1: '#fff', 2: '#1d2024', 3: '#fff', 4: '#fff', 5: '#1d2024', 6: '#1d2024'}
FACE = {'right': 0, 'left': 1, 'bottom': 2, 'top': 3, 'front': 4, 'back': 5}
INK = '#1d2024'
MUTED = '#5c636b'
FONT = 'font-family="system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial, sans-serif"'
S = 34  # face side
D = 16  # depth offset of the oblique faces
CELL_W = 196
CELL_H = 164
MARGIN = 54


def number(value):
    return str(int(value)) if float(value).is_integer() else repr(value)


def cyclic_key(triple):
    return min(triple, triple[1:] + triple[:1], triple[2:] + triple[:2])


def read_corners():
    corners = {}
    for line in (RESULTS / 'tableau.txt').read_text().splitlines():
        if line and not line.startswith('#'):
            name, *triples = line.split()
            corners[name] = {cyclic_key(tuple(map(int, t))) for t in triples}
    return corners


def polygon(colour, points, tx, ty, size=15):
    coordinates = ' '.join(f'{number(x)},{number(y)}' for x, y in points)
    return (
        f'<polygon points="{coordinates}" fill="{FACE_COLOURS[colour]}" stroke="{INK}" '
        'stroke-width="1.2" stroke-linejoin="round"/>'
        f'<text x="{number(tx)}" y="{number(ty + size * 0.36)}" text-anchor="middle" '
        f'font-size="{size}" font-weight="700" fill="{FACE_INK[colour]}" {FONT}>{colour}</text>'
    )


def square(colour, x, y):
    return polygon(colour, [(x, y), (x + S, y), (x + S, y + S), (x, y + S)], x + S / 2, y + S / 2)


def cube(name, colours, corners, x, y):
    side = {key: colours[index] for key, index in FACE.items()}

    # Reading a visible corner clockwise from outside must give one of this
    # cube's corners in Table 3 of Johnson and Roldan; reversed, none of them.
    clockwise = cyclic_key((side['top'], side['right'], side['front']))
    reversed_corner = cyclic_key((side['top'], side['front'], side['right']))
    if clockwise not in corners[name] or reversed_corner in corners[name]:
        raise ValueError(f'{name}: wrong handedness')

    fx = x + S
    fy = y + D
    return ''.join([
        square(side['left'], x, fy),
        square(side['bottom'], fx, fy + S),
        polygon(side['top'], [(fx, fy), (fx + D, y), (fx + S + D, y), (fx + S, fy)],
                fx + (S + D) / 2, y + D / 2, 12),
        polygon(side['right'], [(fx + S, fy), (fx + S + D, y), (fx + S + D, y + S), (fx + S, fy + S)],
                fx + S + D / 2, y + (S + D) / 2, 12),
        square(side['back'], fx + S + D, y),
        square(side['front'], fx, fy),
        f'<text x="{fx + S + D + 4}" y="{fy + S + 26}" font-size="19" font-weight="600" '
        f'fill="{INK}" {FONT}>{name}</text>',
    ])


def main():
    cubes = json.loads((RESULTS / 'geometry.json').read_text())['cubes']
    corners = read_corners()
    width = MARGIN + 6 * CELL_W + 8
    height = MARGIN + 6 * CELL_H + 8
    parts = [f'<rect width="{width}" height="{height}" fill="#fff"/>']
    for i, label in enumerate(LABELS):
        parts.append(f'<text x="{MARGIN + i * CELL_W + CELL_W // 2 - 8}" y="34" text-anchor="middle" '
                     f'font-size="24" font-weight="600" fill="{MUTED}" {FONT}>{label.lower()}</text>')
        parts.append(f'<text x="24" y="{MARGIN + i * CELL_H + CELL_H // 2}" text-anchor="middle" '
                     f'font-size="24" font-weight="600" fill="{MUTED}" {FONT}>{label}</text>')
    for r, row in enumerate(LABELS):
        for c, column in enumerate(LABELS):
            x = MARGIN + c * CELL_W
            y = MARGIN + r * CELL_H
            if r == c:
                parts.append(f'<rect x="{x}" y="{y}" width="{CELL_W - 14}" height="{CELL_H - 14}" '
                             'rx="6" fill="#efece5"/>')
            else:
                name = row + column.lower()
                parts.append(cube(name, cubes[name], corners, x + 12, y + 8))
    OUTPUT.write_text(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" '
        f'height="{height}" role="img" aria-label="The thirty MacMahon cubes, each opened out to '
        f"show all six faces, arranged in Conway's tableau\">{''.join(parts)}</svg>\n"
    )
    print(f'wrote {OUTPUT.relative_to(ROOT)}: 30 cubes, handedness agrees with Table 3')


if __name__ == '__main__':
    main()
