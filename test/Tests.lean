import MyPackage

def main (args : List String) : IO UInt32 := do
  try
    MyPackage.sayHello "world"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

