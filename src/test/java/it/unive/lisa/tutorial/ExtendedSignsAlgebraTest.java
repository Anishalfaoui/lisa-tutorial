package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import org.junit.Assert;
import org.junit.Test;

public class ExtendedSignsAlgebraTest {

    @Test
    public void testPartialOrder() throws SemanticException {
        Assert.assertTrue(ExtendedSigns.STRICTLY_NEGATIVE.lessOrEqual(ExtendedSigns.NEGATIVE));
        Assert.assertTrue(ExtendedSigns.ZERO.lessOrEqual(ExtendedSigns.NEGATIVE));
        Assert.assertTrue(ExtendedSigns.ZERO.lessOrEqual(ExtendedSigns.POSITIVE));
        Assert.assertTrue(ExtendedSigns.STRICTLY_POSITIVE.lessOrEqual(ExtendedSigns.NON_ZERO));

        Assert.assertFalse(ExtendedSigns.NON_ZERO.lessOrEqual(ExtendedSigns.NEGATIVE));
        Assert.assertFalse(ExtendedSigns.NEGATIVE.lessOrEqual(ExtendedSigns.NON_ZERO));
    }

    @Test
    public void testLubs() throws SemanticException {
        Assert.assertEquals(ExtendedSigns.NEGATIVE, ExtendedSigns.ZERO.lub(ExtendedSigns.STRICTLY_NEGATIVE));
        Assert.assertEquals(ExtendedSigns.POSITIVE, ExtendedSigns.ZERO.lub(ExtendedSigns.STRICTLY_POSITIVE));
        Assert.assertEquals(ExtendedSigns.TOP, ExtendedSigns.NON_ZERO.lub(ExtendedSigns.ZERO));
        Assert.assertEquals(ExtendedSigns.STRICTLY_POSITIVE, ExtendedSigns.BOTTOM.lub(ExtendedSigns.STRICTLY_POSITIVE));
    }
}
