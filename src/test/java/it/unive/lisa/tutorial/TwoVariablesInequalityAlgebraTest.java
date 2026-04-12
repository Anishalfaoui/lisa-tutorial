package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.UnaryExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.symbolic.value.operator.binary.NumericNonOverflowingAdd;
import it.unive.lisa.symbolic.value.operator.binary.NumericNonOverflowingMul;
import it.unive.lisa.symbolic.value.operator.binary.NumericNonOverflowingSub;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.type.Untyped;
import org.junit.Assert;
import org.junit.Test;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class TwoVariablesInequalityAlgebraTest {

    private static final SyntheticLocation LOC = SyntheticLocation.INSTANCE;

    private static Variable var(String name) {
        return new Variable(Untyped.INSTANCE, name, LOC);
    }

    private static Constant intConst(int value) {
        return new Constant(Untyped.INSTANCE, value, LOC);
    }

    private static BinaryExpression le(SymbolicExpression left, SymbolicExpression right) {
        return new BinaryExpression(Untyped.INSTANCE, left, right, ComparisonLe.INSTANCE, LOC);
    }

    private static BinaryExpression add(SymbolicExpression left, SymbolicExpression right) {
        return new BinaryExpression(Untyped.INSTANCE, left, right, NumericNonOverflowingAdd.INSTANCE, LOC);
    }

    private static BinaryExpression sub(SymbolicExpression left, SymbolicExpression right) {
        return new BinaryExpression(Untyped.INSTANCE, left, right, NumericNonOverflowingSub.INSTANCE, LOC);
    }

    private static BinaryExpression mul(SymbolicExpression left, SymbolicExpression right) {
        return new BinaryExpression(Untyped.INSTANCE, left, right, NumericNonOverflowingMul.INSTANCE, LOC);
    }

    private static UnaryExpression neg(SymbolicExpression expression) {
        return new UnaryExpression(Untyped.INSTANCE, expression, NumericNegation.INSTANCE, LOC);
    }

    @Test
    public void testBoundaryLatticeBehavior() throws SemanticException {
        Assert.assertTrue(TwoVariablesInequality.BOTTOM.lessOrEqual(TwoVariablesInequality.TOP));
        Assert.assertFalse(TwoVariablesInequality.TOP.lessOrEqual(TwoVariablesInequality.BOTTOM));

        Assert.assertTrue(TwoVariablesInequality.TOP.lub(TwoVariablesInequality.BOTTOM).isTop());
        Assert.assertTrue(TwoVariablesInequality.TOP.glb(TwoVariablesInequality.BOTTOM).isBottom());
    }

    @Test
    public void testEmptySetRepresentsTop() throws SemanticException {
        TwoVariablesInequality fromEmpty = new TwoVariablesInequality(new HashSet<>());
        Assert.assertTrue(fromEmpty.isTop());
        Assert.assertTrue(fromEmpty.close().isTop());
    }

    @Test
    public void testLubKeepsOnlyCommonUpperBounds() throws SemanticException {
        Variable x = var("x");
        TwoVariablesInequality leftBranch = TwoVariablesInequality.TOP.assume(le(x, intConst(0)), null, null, null);
        TwoVariablesInequality rightBranch = TwoVariablesInequality.TOP.assume(le(x, intConst(10)), null, null, null);

        TwoVariablesInequality merged = leftBranch.lub(rightBranch);
        Assert.assertTrue(leftBranch.lessOrEqual(merged));
        Assert.assertTrue(rightBranch.lessOrEqual(merged));
        Assert.assertEquals(Satisfiability.SATISFIED, merged.satisfies(le(x, intConst(10)), null, null));
        Assert.assertEquals(Satisfiability.UNKNOWN, merged.satisfies(le(x, intConst(0)), null, null));
    }

    @Test
    public void testAssignPerformsStrongUpdate() throws SemanticException {
        Variable x = var("x");
        TwoVariablesInequality beforeAssign = TwoVariablesInequality.TOP.assume(le(x, intConst(0)), null, null, null);

        TwoVariablesInequality afterAssign = beforeAssign.assign(x, intConst(5), null, null);
        Assert.assertFalse(afterAssign.isBottom());
        Assert.assertEquals(Satisfiability.SATISFIED, afterAssign.satisfies(le(x, intConst(5)), null, null));
        Assert.assertEquals(Satisfiability.UNKNOWN, afterAssign.satisfies(le(x, intConst(0)), null, null));
    }

    @Test
    public void testContradictionIsDetectedAsBottom() {
        Map<Variable, Double> emptyCoefficients = new HashMap<>();
        TwoVariablesInequality.LinearInequality contradiction =
                new TwoVariablesInequality.LinearInequality(Collections.unmodifiableMap(emptyCoefficients), -1.0);

        TwoVariablesInequality domain = new TwoVariablesInequality(Collections.singleton(contradiction));
        Assert.assertTrue(domain.isBottom());
    }

    @Test
    public void testAssumeParsingHandlesNormalizedLinearForms() throws SemanticException {
        Variable x = var("x");
        Variable y = var("y");

        BinaryExpression first = le(sub(x, y), intConst(3));
        BinaryExpression second = le(add(neg(x), y), intConst(2));
        BinaryExpression third = le(sub(mul(intConst(2), x), y), intConst(7));

        TwoVariablesInequality state = TwoVariablesInequality.TOP
                .assume(first, null, null, null)
                .assume(second, null, null, null)
                .assume(third, null, null, null);

        Assert.assertEquals(Satisfiability.SATISFIED, state.satisfies(first, null, null));
        Assert.assertEquals(Satisfiability.SATISFIED, state.satisfies(second, null, null));
        Assert.assertEquals(Satisfiability.SATISFIED, state.satisfies(third, null, null));
    }

    @Test
    public void testClosureFixpointDerivesMultiStepTransitivity() throws SemanticException {
        Variable x = var("x");
        Variable y = var("y");
        Variable z = var("z");
        Variable w = var("w");

        BinaryExpression xLeYPlus1 = le(sub(x, y), intConst(1));
        BinaryExpression yLeZPlus1 = le(sub(y, z), intConst(1));
        BinaryExpression zLeWPlus1 = le(sub(z, w), intConst(1));
        BinaryExpression expected = le(sub(x, w), intConst(3));

        TwoVariablesInequality chained = TwoVariablesInequality.TOP
                .assume(xLeYPlus1, null, null, null)
                .assume(yLeZPlus1, null, null, null)
                .assume(zLeWPlus1, null, null, null)
                .close();

        Assert.assertEquals(Satisfiability.SATISFIED, chained.satisfies(expected, null, null));
    }

    @Test
    public void testSmallStepSemanticsCanonicalizesState() throws SemanticException {
        Variable x = var("x");
        Variable y = var("y");
        BinaryExpression expression = le(sub(x, y), intConst(1));

        TwoVariablesInequality state = TwoVariablesInequality.TOP.assume(expression, null, null, null);
        TwoVariablesInequality stepped = state.smallStepSemantics(expression, null, null);

        Assert.assertTrue(state.lessOrEqual(stepped));
        Assert.assertTrue(stepped.lessOrEqual(state));
    }
}
