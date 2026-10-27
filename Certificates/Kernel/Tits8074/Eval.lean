module

public import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz_eval CertificateChecks.KernelT8074E
  "Certificates/Kernel/Tits8074/data/c8074s.json.gz" 92160 14630952304977141771
  (sg : Array (Array Nat)) (hw : List (List Nat)) (tg : List (List Nat)) (ps : List Nat)

namespace CertificateChecks.KernelT8074E

def invI (g : Array Nat) : Array Nat :=
  (List.range 1755).foldl (fun r i => r.set! g[i]! i) (Array.replicate 1755 0)

def letterI (c : Nat) : Array Nat :=
  if c % 2 == 0 then sg[c / 2]! else invI sg[c / 2]!

def wordI (w : List Nat) : Array Nat :=
  w.foldr (fun c acc => let g := letterI c; acc.map fun x => g[x]!) (Array.range 1755)

def hGen : Array (Array Nat) := (hw.map wordI).toArray

def tGen : Array (Array Nat) := (tg.map wordI).toArray

end CertificateChecks.KernelT8074E

end
