module

public import Certificates.Data.G23RecogTriInputs
public import Certificates.Kernel.Bounds.Family

open CFSG.GH74.QTGen4.Recog.G23.P7 CFSG.CosetTable

public section

#kb_family "data/F320013.json.gz" 36792 2269583736716670341 (r0 := triWords)
  (r1 := restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords) (cfgWords := cfgWords)
  (r3 := fun a b => restrictWords (subsetOf 6 [0, 1, 2, 3]) (cfgWords a b))

end
