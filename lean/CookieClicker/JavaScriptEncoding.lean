import CookieClicker.JavaScriptEval

/-! UTF-16 URI, legacy escape, and browser base64 operations. Invalid UTF-8,
unpaired URI input surrogates, and invalid base64 are explicit exceptions.
-/
namespace CookieClicker.JavaScript.Encoding

private def ascii (s : String) : List Nat := s.toList.map Char.toNat
private def alphaNumeric (n : Nat) :=
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)
private def hex (n : Nat) := if n < 10 then n + 48 else n + 55
private def unhex (n : Nat) : Option Nat :=
  if 48 ≤ n && n ≤ 57 then some (n-48)
  else if 65 ≤ n && n ≤ 70 then some (n-55)
  else if 97 ≤ n && n ≤ 102 then some (n-87) else none
private def percent (n : Nat) : JSString := [37, UInt16.ofNat (hex (n/16)), UInt16.ofNat (hex (n%16))]
private def units (point : Nat) : JSString :=
  if point < 0x10000 then [UInt16.ofNat point]
  else [UInt16.ofNat (0xd800+(point-0x10000)/1024), UInt16.ofNat (0xdc00+(point-0x10000)%1024)]
private def bytes (point : Nat) : List Nat :=
  if point < 128 then [point]
  else if point < 2048 then [192+point/64,128+point%64]
  else if point < 65536 then [224+point/4096,128+(point/64)%64,128+point%64]
  else [240+point/262144,128+(point/4096)%64,128+(point/64)%64,128+point%64]
private def reserved := ascii ";/?:@&=+$,#"

def encodeURI (input : JSString) (component : Bool) : Except String JSString := do
  let data := input.toArray
  let mut output := []
  let mut index := 0
  for _ in List.range data.size do
    if index < data.size then
      let first := (data[index]?.getD 0).toNat
      if alphaNumeric first || (ascii "-_.!~*'()").contains first || (!component && reserved.contains first) then
        output := output ++ [UInt16.ofNat first]
        index := index+1
      else
        let mut point := first
        index := index+1
        if 0xdc00 ≤ first && first ≤ 0xdfff then throw "Malformed URI input surrogate"
        if 0xd800 ≤ first && first ≤ 0xdbff then
          let second := (data[index]?.getD 0).toNat
          if !(0xdc00 ≤ second && second ≤ 0xdfff) then throw "Malformed URI input surrogate"
          point := 0x10000+(first-0xd800)*1024+second-0xdc00
          index := index+1
        output := output ++ (bytes point).flatMap percent
  return output

private def readByte (data : Array UInt16) (index : Nat) : Except String Nat := do
  if data[index]? != some 37 then throw "Malformed URI escape"
  let some a := data[index+1]? >>= (unhex ∘ UInt16.toNat) | throw "Malformed URI escape"
  let some b := data[index+2]? >>= (unhex ∘ UInt16.toNat) | throw "Malformed URI escape"
  return a*16+b

def decodeURI (input : JSString) (component : Bool) : Except String JSString := do
  let data := input.toArray
  let mut output := []
  let mut index := 0
  for _ in List.range data.size do
    if index < data.size then
      let first := data[index]?.getD 0
      if first != 37 then
        output := output ++ [first]
        index := index+1
      else
        let initial := index
        let byte ← readByte data index
        index := index+3
        if byte < 128 then
          output := output ++ (if !component && reserved.contains byte then (input.drop initial).take 3 else [UInt16.ofNat byte])
        else
          let count ← if 194 ≤ byte && byte ≤ 223 then pure 2
            else if 224 ≤ byte && byte ≤ 239 then pure 3
            else if 240 ≤ byte && byte ≤ 244 then pure 4
            else throw "Malformed URI UTF-8 lead"
          let mut point := byte % (2^(7-count))
          for _ in List.range (count-1) do
            let next ← readByte data index
            if !(128 ≤ next && next ≤ 191) then throw "Malformed URI UTF-8 continuation"
            point := point*64+next-128
            index := index+3
          let minimum := if count == 2 then 128 else if count == 3 then 2048 else 65536
          if point < minimum || point > 0x10ffff || (0xd800 ≤ point && point ≤ 0xdfff) then
            throw "Malformed URI UTF-8 point"
          output := output ++ units point
  return output

def escape (input : JSString) : JSString := input.flatMap fun unit =>
  let n := unit.toNat
  if alphaNumeric n || (ascii "@*_+-./").contains n then [unit]
  else if n < 256 then percent n
  else [37,117,UInt16.ofNat (hex (n/4096)),UInt16.ofNat (hex ((n/256)%16)),
    UInt16.ofNat (hex ((n/16)%16)),UInt16.ofNat (hex (n%16))]

private def hexRun (input : Array UInt16) (index count : Nat) : Option Nat :=
  (List.range count).foldlM (fun value offset => do
    let unit ← input[index+offset]?
    let digit ← unhex unit.toNat
    pure (value*16+digit)) 0

def unescape (input : JSString) : JSString := Id.run do
  let data := input.toArray
  let mut output := []
  let mut index := 0
  for _ in List.range data.size do
    if index < data.size then
      let first := data[index]?.getD 0
      let decoded := if first == 37 then
          if data[index+1]? == some 117 then (hexRun data (index+2) 4).map (fun n => (n,6))
          else (hexRun data (index+1) 2).map (fun n => (n,3))
        else none
      match decoded with
      | some (n,size) => output := output ++ [UInt16.ofNat n]; index := index+size
      | none => output := output ++ [first]; index := index+1
  return output

private def alphabet := ascii "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
private def base64Char (index : Nat) : UInt16 := UInt16.ofNat (alphabet[index]?.getD 0)

def btoa (input : JSString) : Except String JSString := do
  if input.any (fun unit => unit.toNat > 255) then throw "Base64 input contains a non-byte character"
  let data := input.toArray
  let mut output := []
  for chunk in List.range ((data.size+2)/3) do
    let start := chunk*3
    let a := (data[start]?.getD 0).toNat
    let b := (data[start+1]?.getD 0).toNat
    let c := (data[start+2]?.getD 0).toNat
    output := output ++ [base64Char (a/4),base64Char ((a%4)*16+b/16),
      if start+1 < data.size then base64Char ((b%16)*4+c/64) else 61,
      if start+2 < data.size then base64Char (c%64) else 61]
  return output

def atob (input : JSString) : Except String JSString := do
  let mut data := input.filter (fun unit => ![9,10,12,13,32].contains unit.toNat)
  if data.length % 4 == 0 then
    if data.getLast? == some 61 then data := data.dropLast
    if data.getLast? == some 61 then data := data.dropLast
  if data.length % 4 == 1 then throw "Invalid base64 length"
  let mut output := []
  let mut buffer := 0
  let mut count := 0
  for unit in data do
    let some value := alphabet.idxOf? unit.toNat | throw "Invalid base64 character"
    buffer := buffer*64+value
    count := count+6
    if count ≥ 8 then
      count := count-8
      output := output ++ [UInt16.ofNat (buffer/(2^count))]
      buffer := buffer%(2^count)
  return output

def operate (name : String) (input : JSString) : Except (String × String) JSString :=
  if name == "escape" then .ok (escape input)
  else if name == "unescape" then .ok (unescape input)
  else if name == "btoa" then (btoa input).mapError (fun e => ("InvalidCharacterError",e))
  else if name == "atob" then (atob input).mapError (fun e => ("InvalidCharacterError",e))
  else if name == "encodeURI" || name == "encodeURIComponent" then
    (encodeURI input (name == "encodeURIComponent")).mapError (fun e => ("URIError",e))
  else if name == "decodeURI" || name == "decodeURIComponent" then
    (decodeURI input (name == "decodeURIComponent")).mapError (fun e => ("URIError",e))
  else .error ("TypeError","Unknown encoding operation")

def resume (m : Machine) (c : BuiltinContinuation) (value : Value) : Machine :=
  if isObject value then primitiveThen m value "string" (.builtin c)
  else checked m (toJSString value) fun input =>
    match operate c.id.name input with
    | .ok output => result m (textResult [value] output)
    | .error (name,message) => fail m (.exception name message)

def dispatch (m : Machine) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  if construct then fail m (.exception "TypeError" "Encoding operation is not a constructor")
  else resume m { id := ⟨"Encoding",id.name⟩, phase := "input", thisValue := receiver, arguments }
    (arguments[0]?.getD .undefined)

end CookieClicker.JavaScript.Encoding
