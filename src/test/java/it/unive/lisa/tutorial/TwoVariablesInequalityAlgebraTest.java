package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import org.junit.Assert;
import org.junit.Test;

import java.util.HashSet;

public class TwoVariablesInequalityAlgebraTest {

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
}
