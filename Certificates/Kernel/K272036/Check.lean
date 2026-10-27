module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SigmaCheckData

public section

namespace CertificateChecks.K272036

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def r3s : List (List (Fin 5 × Bool)) :=
  [[(3, true), (0, false), (3, false), (0, false), (3, true), (1, false)],
   [(3, true), (0, true), (3, true), (0, true)]]

@[expose] def r4s : List (List (Fin 5 × Bool)) :=
  [[(0, true), (1, true), (4, true), (0, true), (4, true)],
   [(4, true), (4, true), (4, true)]]

@[expose] def r5s : List (List (Fin 5 × Bool)) :=
  [[(2, true), (3, true), (4, false), (3, true), (4, false)],
   [(3, false), (4, false), (0, true), (3, false), (4, false), (0, true)]]

@[expose] def c3w : List (List (Fin 5 × Bool)) :=
  [[(3, true)], [(0, true), (3, false)], [(0, false), (1, true)], [(3, false), (0, true)],
   [(2, true), (3, false), (4, false)], [(0, true), (2, true), (4, true), (3, true)],
   [(2, true), (4, true), (0, false), (3, false)]]

@[expose] def c4w : List (List (Fin 5 × Bool)) :=
  [[(4, true)], [(0, true), (1, true), (4, false)], [(0, true), (4, true), (0, false)]]

@[expose] def relsOK (g : Fin 5 → ShC) (rs : List (List (Fin 5 × Bool))) : Bool :=
  rs.all fun r => shEval g r == shOne

@[expose] def inWords (ws : List (List (Fin 5 × Bool))) (s : ShC) : Bool :=
  ws.any fun w => shEval shGen w == s

@[expose] def stageABWith (ws3 ws4 : List (List (Fin 5 × Bool))) : Bool :=
  relsOK shGen (r3s ++ r4s ++ r5s) &&
  shK.all fun s =>
    (!relsOK (shS s shOne) r3s || inWords ws3 s) && (!relsOK (shS shOne s) r4s || inWords ws4 s)

@[expose] def sqOK (w3 w4 : List (Fin 5 × Bool)) : Bool :=
  let s := shS (shEval shGen w3) (shEval shGen w4)
  shEval s w3 == shAd (shGen 3) && shEval s w4 == shAd (shGen 4)

@[expose] def stageCWith (sq : Bool) : Bool :=
  c3w.all fun w3 => c4w.all fun w4 =>
    shEval shGen w3 == shT || !relsOK (shS (shEval shGen w3) (shEval shGen w4)) r5s ||
      (sq && !sqOK w3 w4)

theorem stageAB : stageABWith c3w c4w = true := by decide +kernel

theorem stageC : stageCWith true = true := by decide +kernel

end CertificateChecks.K272036

end
