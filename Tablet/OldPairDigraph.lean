import Tablet.LoopGraph
import Tablet.LooplessDigraph

-- [TABLET NODE: OldPairDigraph]
def OldPairDigraph (G : LoopGraph) : LooplessDigraph := by
-- BODY
  letI : Fintype G.vertex := G.fintype
  letI : DecidableRel G.adj := G.decidableAdj
  exact {
    vertex := {p : G.vertex × G.vertex // ¬ G.adj p.1 p.2}
    fintype := inferInstance
    arc := fun u v => G.adj u.1.1 v.1.2
    decidableArc := inferInstance
    loopless := by
      intro u hu
      exact u.2 hu
  }
