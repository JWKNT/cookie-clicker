/-! Explicit cookie-origin configuration. File mode uses the pinned Chromium
cookieable-scheme defaults, which exclude file URLs. HTTP cookie stores and
changes to the native scheme registry require a separate model. -/
namespace CookieClicker.JavaScript.BrowserCookieState

inductive Origin where
  | unconfigured
  | file
  | opaqueOrigin
  deriving Repr, DecidableEq

end CookieClicker.JavaScript.BrowserCookieState
