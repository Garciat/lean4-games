"""
This script converts a JSON file containing game data into Lean 4 files.
The JSON file should have the following structure:
{
    "data": {
        "world1": {
            "level1": {
                "code": "lean code for level 1"
            },
            "level2": {
                "code": "lean code for level 2"
            }
        },
        "world2": {
            "level1": {
                "code": "lean code for level 3"
            }
        }
    }
}
"""

import json
import sys

if len(sys.argv) < 3:
    print("Usage: python lean4game.py <json_file> <destination>")
    sys.exit(1)

with open(sys.argv[1], 'r') as f:
    game = json.load(f)

game_data = game['data']

for world in game_data:
    for level in game_data[world]:
        code = game_data[world][level]['code']

        if not code.endswith('\n'):
            code += '\n'

        target_path = f"{sys.argv[2]}/{world}_{level}.lean"
        with open(target_path, 'w') as f:
            f.write(code)
            print(target_path)
