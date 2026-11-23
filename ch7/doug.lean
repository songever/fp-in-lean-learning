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

-- Using a Custom Monad
def ConfigIO (α : Type) : Type :=
  Config → IO α
-- Used as Env Monad Reader in ch5.2. Arithmetic in Monads
instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg -- extract the result α from cfg
    next v cfg         -- keep operation on cfg to get IO β
-- Running a ConfigIo action involves transforming it into an
-- IO action by providing it with a configuration:
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
-- the next step is to define a means of accessing the current
-- configuration as part of ConfigIO:
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg  -- IO's pure
-- override a configuration:
--  "locally" describes the action taken in mutated config's scope
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
-- ordinary IO actions inserted in ConfigIO:
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action

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
def Config.fileName (cfg :Config) (file : String) :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"
def Config.dirName (cfg :Config) (dir : String) :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

-- do on [ConfigIO : Monad], (← ConfigIO α) give out an α
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))
def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *> doList xs action

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← runIO path.readDir
    locally (·.inDirectory)
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

-- the advantages of ConfigIO over passing cfg manually:
-- 1. It is easier to ensure that configurations are passed down
--    unchanged, except when changes are desired
-- 2. The concern of passing the configuration onwards is more
--    clearly separated from the concern of printing directory
--    contents
-- 3. As the program grows, there will be more and more inter-
--    mediate layers that do nothing with configurations except
--    propagate them, and these layers don't need to be rewritten
--    as the configuration logic changes

-- downsides:
-- 1. As the program evolves and the monad requires more features,
--    each of the basic operators such as locally and currentConfig
--    will need to be updated
-- 2. Wrapping ordinary IO actions in runIO is noisy and distracts
--    from the flow of the program
-- 3. Writing monads instances by hand is repetitive, and the
--    technique for adding a reader effect to another monad is
--    a design pattern that requires documentation and
--    communication overhead

-- Using a technique called monad transformers, all of these
-- downsides can be addressed.
