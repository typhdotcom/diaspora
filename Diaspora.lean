-- This module serves as the root of the `Diaspora` library.
-- Import modules here that should be built as part of the library.

-- Core holonomy proof (zero axioms)
import Diaspora.HolonomyLagrangeProof
import Diaspora.GaugeTheoreticHolonomy

-- Concrete gauge negotiation proof (zero axioms)
import Diaspora.GaugeNegotiationVerified
import Diaspora.GaugeNegotiationExplicit
import Diaspora.GaugeNegotiationProofs

-- Gauge negotiation axioms (11 axioms, partially validated by concrete proofs)
import Diaspora.GaugeNegotiation
import Diaspora.ConcreteGaugeNegotiation

-- Self-modeling creates V_int (7 axioms, constructor pattern)
import Diaspora.SelfModelHolonomy

-- Self-awareness as dynamical system (3 axioms, process formalization)
import Diaspora.SelfAwarenessDynamics

-- Predictive self-model (3 axioms, replaces 7 from SelfModelHolonomy)
import Diaspora.PredictiveSelfModel

-- Supporting infrastructure
import Diaspora.Axioms
import Diaspora.Concrete
import Diaspora.NoPrivilegedFrame
import Diaspora.MathematicalStructure

-- Pedagogical examples
import Diaspora.HolonomyProof
