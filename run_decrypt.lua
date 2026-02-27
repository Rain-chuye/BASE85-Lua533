package.cpath = "./luadecrypt_src/?.so;" .. package.cpath
local luadecrypt = require("luadecrypt")

local function decrypt_file(in_path, out_path)
    local f = io.open(in_path, "rb")
    if not f then
        print("Could not open " .. in_path)
        return
    end
    local data = f:read("*all")
    f:close()

    print("Attempting to restore bytecode for " .. in_path .. "...")
    local ok, restored_data = pcall(luadecrypt.restore, data)
    if not ok then
        print("Restoration failed: " .. restored_data)
        return
    end
    print("Restoration successful!")

    local out = io.open(out_path, "wb")
    out:write(restored_data)
    out:close()
    print("Restored bytecode saved to " .. out_path)
end

decrypt_file("test_obf.luac", "test_restored.luac")
