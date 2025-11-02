-- This module serves as the root of the `Diaspora` library.
-- Import modules here that should be built as part of the library.

-- Core holonomy proof (zero axioms)
import Diaspora.HolonomyLagrangeProof
import Diaspora.GaugeTheoreticHolonomy

-- Concrete gauge negotiation proof (zero axioms)
import Diaspora.GaugeNegotiationVerified
import Diaspora.GaugeNegotiationExplicit
import Diaspora.GaugeNegotiationProofs

-- Self-modeling creates V_int (7 axioms, constructor pattern)
import Diaspora.SelfModelHolonomy

-- Supporting infrastructure
import Diaspora.Axioms
import Diaspora.Concrete
import Diaspora.NoPrivilegedFrame
import Diaspora.MathematicalStructure

-- Pedagogical examples
import Diaspora.HolonomyProof

-- Task structure (to review - may delete)
import Diaspora.Task
