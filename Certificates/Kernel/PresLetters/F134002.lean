module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTreeFact
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.ExtendData
public import Certificates.Kernel.Bounds.Family
public import CFSG.Foundations.Basic
public import Mathlib

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

public section

#kb_family "data/F134002.json.gz" 31319 7896727339651437341
  (r0 := fun a => ((extendTree.collapses extendRels).getD a []).map FreeGroup.toWord)

end
