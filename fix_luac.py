import sys

with open('lua_vm/lua/luac.c', 'r') as f:
    lines = f.readlines()

new_lines = []
skip = False
for line in lines:
    if '/* Pattern 1: Ra = Rb.Rc; Ra = Ra + Rd -> Ra = FUSE_GETADD(Rb, Rc, Rd) */' in line:
        skip = True
    if skip and '}' in line:
        skip = False
        continue
    if not skip:
        new_lines.append(line)

with open('lua_vm/lua/luac.c', 'w') as f:
    f.writelines(new_lines)
