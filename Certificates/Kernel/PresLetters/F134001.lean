module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTreeFact
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StarData
public import Certificates.Kernel.Bounds.Family
public import CFSG.Foundations.Basic
public import Mathlib

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

public section

#kb_family "data/F134001.json.gz" 41961 16478068081402879829
  (r0 := fun a => ((starTree.collapses starRels).getD a []).map FreeGroup.toWord)

end
