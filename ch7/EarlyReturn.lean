-- command-line applicaitons that terminate early if the arguments
-- or input are incorrect.

def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trimAscii
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0
-- Using early return avoids needing to nest the control flow.

-- do occurs underneath some other structures:
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
