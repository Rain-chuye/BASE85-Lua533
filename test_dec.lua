local luadec = require("luadec")
local function read_file(name)
    local f = io.open(name, "rb")
    if not f then return nil end
    local data = f:read("*a")
    f:close()
    return data
end
local function write_file(name, data)
    local f = io.open(name, "wb")
    if f then f:write(data) f:close() end
end
local obfuscated = read_file("test.obf.luac")
if not obfuscated then
    print("Error: test.obf.luac not found.")
    os.exit(1)
end
print("Decrypting...")
local standard = luadec.decrypt(obfuscated)
write_file("test.standard.luac", standard)
print("Saved to test.standard.luac")
local f, err = load(standard)
if f then
    print("Standard bytecode loaded successfully!")
    f()
else
    print("Failed to load standard bytecode: " .. tostring(err))
end
