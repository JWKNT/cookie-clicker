import CookieClicker.JavaScriptBrowser

open CookieClicker.JavaScript CookieClicker.JavaScript.Browser

private def get {α : Type} (value : Checked α) : IO α :=
  match value with
  | .ok value => pure value
  | .error failure => throw (IO.userError (reprStr failure))

private def verify (value : Bool) (message : String) : IO Unit :=
  if value then pure () else throw (IO.userError message)

def main : IO Unit := do
  -- Exercise the actual parser-output allocator even though the public strict
  -- HTML grammar currently rejects audio insertion before reaching it.
  let (ids,state) ← get (allocateParsed initial 10 [
    .element "audio" [⟨"autoplay",[]⟩] []])
  let id := ids.head!
  let node ← get (checkedNode state id)
  verify (!node.mediaPlaybackPristine) "Parsed autoplay did not invalidate provenance"
  let removed ← get (replaceNode state id {node with attributes := []})
  let after ← get (checkedNode removed id)
  verify (!after.mediaPlaybackPristine) "Removal restored parsed playback provenance"
  -- The extra old-attribute guard also protects direct initial-state imports.
  let old := {node with mediaPlaybackPristine := true}
  let imported := {state with nodes := state.nodes.set! id old}
  let removed ← get (replaceNode imported id {old with attributes := []})
  let after ← get (checkedNode removed id)
  verify (!after.mediaPlaybackPristine) "Old autoplay attribute did not invalidate provenance"
  IO.println "3/3 allocator/autoplay provenance checks passed"
