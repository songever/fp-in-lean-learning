-- 7.1. Combing IO and Reader
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs :  List String → Option Config
| [] => some {} -- both fields default
| ["--ascii"] => some {useASCII := true}
| _ => none

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name => pure (some (if (← path.isDir) then .dir name else .file name))

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"
def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

-- Adding a Reader to Any Monad

--Monad transformers consist of:
-- 1. A definition of the transformer itself, which is typically
--    a function from types to types
-- 2. A Monad instance that assumes the inner type is already a
--    monad
-- 3. An operator to "lift" an action from the inner monad to the
--    transformed monad, akin to runIO

-- def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
--   ρ → m α

-- ρ is the environment that is accessible to the reader
-- m is the monad that is being transformed, such as IO
-- α is the type of values being returned by the monadic
--   computation Both α and ρ are in the same universe because
--   the operator that retrieves the environment in the monad
--   will have type m ρ

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

-- class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v) where
--   read : m ρ
instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env
export MonadReader (read)
-- the target monad IO has been replaced by some arbitrary m
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env

-- to eliminate the uses of "runIO":
-- class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
--   monadLift : {α : Type u} → m α → n α
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action

-- do on [ConfigIO : Monad], (← read) give out an α
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"
def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"

-- translate the "locally"
-- class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
--   withReader {α : Type u} : (ρ → ρ) → m α → m α
export MonadWithReader (withReader)
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action := fun cfg => action (change cfg)

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *> doList xs action

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← (toEntry path) with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    withReader (·.inDirectory)
      (doList (contents.qsort dirLT).toList fun d =>
        dirTree d.path)

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    (dirTree (← IO.currentDir)).run config
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".intercalate args}\n"
    IO.eprintln usage
    pure 1

#eval main []

-- pros on rewriting with ReaderT:
-- 1. Readers who know about ReaderT don't need to take time to
--    understand the Monad instance for ConfigIO, working backwards
--    to the meaning of monad itself.
-- 2. Adding further effects to the monad (such as a state effect
--    to count the files in each directory and display a count at
--    the end) requires far fewer changes to the code, because the
--    monad transformers and MonadLift instances provided in the
--    library work well together.
-- 3. Using a set of type classes included in the standard library
--    , polymorphic code can be written in such a way that it can
--    work with a variety of monads without having to care about
--    details like the order in which the monad transformers were
--    applied.
