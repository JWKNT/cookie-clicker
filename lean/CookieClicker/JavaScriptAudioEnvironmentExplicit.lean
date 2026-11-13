import CookieClicker.JavaScriptAudioLocals
namespace CookieClicker.JavaScript.AudioEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem identifier_game_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "Game"=
      {({
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } : Machine) with control:=.expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  exact identifier_game {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

theorem identifier_vol_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "vol"=
      {({
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } : Machine) with control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "vol",false⟩)} := by
  exact identifier_vol {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

theorem identifier_volume_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "volume"=
      {({
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } : Machine) with control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "volume",false⟩)} := by
  exact identifier_volume {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

theorem identifier_volumeSetting_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "volumeSetting"=
      {({
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } : Machine) with control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "volumeSetting",false⟩)} := by
  exact identifier_volumeSetting {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

theorem volume_reference_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    identifierReference {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "volume"=
      .ok ⟨.environment (localIndex scopes) "volume",false⟩ := by
  exact volume_reference {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

theorem volumeSetting_reference_explicit (frame : AudioMuted.Frame) (scopes : HasEnvironment.Scopes frame.window)
    (url vol pitch arguments volume setting : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    identifierReference {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "volumeSetting"=
      .ok ⟨.environment (localIndex scopes) "volumeSetting",false⟩ := by
  exact volumeSetting_reference {
      heap := heap frame scopes url vol pitch arguments volume setting
      context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } frame scopes url vol pitch arguments volume setting

end CookieClicker.JavaScript.AudioEnvironment
