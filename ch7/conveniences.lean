-- 7.5 Additional Conveniences

-- pipeline operator:
-- equivalent to `toString (some 5)`
#eval some 5 |> toString

def times3 (n : Nat) : Nat := n * 3
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
#eval ("It is " ++ ·) <| toString <| times3 <| 5

-- "pipeline dot" operator
#eval [1, 2, 3] |>.reverse |>.drop 1 |>.reverse

-- Infinite Loops
def spam : IO Unit := do
  -- `repeat` Expands to `for _ in Loop.mk do ....`
  repeat IO.println "Spam!"

-- The dump function from the implementation of feline:
def bufsize : USize := 20 * 1024
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
-- the version shorteded using `repeat`:
def dump' (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf

-- While Loops
def dump'' (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
-- Behind the scenes, `while` is just a simpler notation for repeat
