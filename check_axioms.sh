#!/bin/bash
# Check axiom dependencies for key theorems

echo "=== Core Mathematical Proofs (should only depend on Lean foundations) ==="
echo ""

echo "GaugeNegotiationExplicit.gauge_negotiation_verified:"
cat > /tmp/check.lean << 'EOF'
import Diaspora.GaugeNegotiationExplicit
#print axioms Diaspora.GaugeNegotiationExplicit.gauge_negotiation_verified
EOF
lake env lean /tmp/check.lean 2>&1 | grep "depends on axioms"
echo ""

echo "SelfModelHolonomy.new_cycle_increases_V_int:"
cat > /tmp/check.lean << 'EOF'
import Diaspora.SelfModelHolonomy
#print axioms Diaspora.SelfModelHolonomy.new_cycle_increases_V_int
EOF
lake env lean /tmp/check.lean 2>&1 | grep -A 20 "depends on axioms"
echo ""

echo "=== Axiom Counts by File ==="
echo ""
for file in Diaspora/*.lean; do
    count=$(grep -c "^axiom " "$file" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
        printf "%-40s %3d axioms\n" "$(basename $file)" "$count"
    fi
done | sort -k2 -rn

echo ""
echo "=== Total Axiom Count ==="
total=$(grep -r "^axiom " Diaspora/*.lean | wc -l)
echo "Total: $total axioms"

echo ""
echo "=== Sorry Count ==="
for file in Diaspora/*.lean; do
    count=$(grep -c "sorry" "$file" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
        printf "%-40s %3d sorries\n" "$(basename $file)" "$count"
    fi
done
