package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Objects;

public class ExtendedSigns implements BaseNonRelationalValueDomain<ExtendedSigns> {

    public static final ExtendedSigns BOTTOM = new ExtendedSigns(Integer.MIN_VALUE);
    public static final ExtendedSigns NEGATIVE = new ExtendedSigns(-2);
    public static final ExtendedSigns STRICTLY_NEGATIVE = new ExtendedSigns(-1);
    public static final ExtendedSigns ZERO = new ExtendedSigns(0);
    public static final ExtendedSigns STRICTLY_POSITIVE = new ExtendedSigns(1);
    public static final ExtendedSigns NON_ZERO = new ExtendedSigns(2);
    public static final ExtendedSigns POSITIVE = new ExtendedSigns(3);
    public static final ExtendedSigns TOP = new ExtendedSigns(Integer.MAX_VALUE);
    public int sign;

    public ExtendedSigns() {
        this.sign = Integer.MAX_VALUE;
    }
    public ExtendedSigns(int sign) {
        this.sign = sign;
    }

    @Override
    public ExtendedSigns top() {
        return TOP;
    }

    @Override
    public ExtendedSigns bottom() {
        return BOTTOM;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        ExtendedSigns that = (ExtendedSigns) o;
        return sign == that.sign;
    }

    @Override
    public int hashCode() {
        return Objects.hash(sign);
    }

    private int mask() {
        if (sign == Integer.MIN_VALUE)
            return 0;
        if (sign == -1)
            return 1;
        if (sign == 0)
            return 2;
        if (sign == -2)
            return 3;
        if (sign == 1)
            return 4;
        if (sign == 2)
            return 5;
        if (sign == 3)
            return 6;
        return 7;
    }

    private static ExtendedSigns fromMask(int mask) {
        switch (mask) {
            case 0:
                return BOTTOM;
            case 1:
                return STRICTLY_NEGATIVE;
            case 2:
                return ZERO;
            case 3:
                return NEGATIVE;
            case 4:
                return STRICTLY_POSITIVE;
            case 5:
                return NON_ZERO;
            case 6:
                return POSITIVE;
            default:
                return TOP;
        }
    }

    @Override
    public boolean lessOrEqualAux(ExtendedSigns other) {
        return (mask() & ~other.mask()) == 0;
    }

    @Override
    public ExtendedSigns lubAux(ExtendedSigns other) {
        return fromMask(mask() | other.mask());
    }

    @Override
    public StructuredRepresentation representation() {
        if (sign == Integer.MAX_VALUE)
            return Lattice.topRepresentation();
        if (sign == Integer.MIN_VALUE)
            return Lattice.bottomRepresentation();
        if (sign == 3)
            return new StringRepresentation(">= 0");
        if (sign == 1)
            return new StringRepresentation("> 0");
        if (sign == -2)
            return new StringRepresentation("<= 0");
        if (sign == -1)
            return new StringRepresentation("< 0");
        if (sign == 0)
            return new StringRepresentation("0");
        if (sign == 2)
            return new StringRepresentation("!= 0");
        return new StringRepresentation("?");
    }

    public boolean isAtLeastPositive(ExtendedSigns other) {
        return other == POSITIVE || other == STRICTLY_POSITIVE;
    }
    @Override
    public ExtendedSigns evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) {
        if (constant.getValue() instanceof Integer) {
            int v = (Integer) constant.getValue();
            if (v > 0) return STRICTLY_POSITIVE;
            else if (v == 0) return ZERO;
            else return STRICTLY_NEGATIVE;
        }
        return top();
    }

    private ExtendedSigns negate() {
        if (this == STRICTLY_NEGATIVE) return STRICTLY_POSITIVE;
        if (this == STRICTLY_POSITIVE) return STRICTLY_NEGATIVE;
        if (this == NEGATIVE) return POSITIVE;
        if (this == POSITIVE) return NEGATIVE;
        return this;
    }

    public ExtendedSigns fromNumberToExtendedSigns(int number) {
        if (number > 0) return STRICTLY_POSITIVE;
        if (number == 0) return ZERO;
        return STRICTLY_NEGATIVE;
    }

    

    @Override
    public ExtendedSigns evalUnaryExpression(UnaryOperator operator, ExtendedSigns arg, ProgramPoint pp, SemanticOracle oracle) {
        if (operator instanceof NumericNegation) return arg.negate();
        return arg;
    }

    public ExtendedSigns inverseLeftSign(ExtendedSigns left, ExtendedSigns right) {
        if(left == STRICTLY_POSITIVE) 
            return right == ZERO ? NEGATIVE : STRICTLY_NEGATIVE;
        if(left == STRICTLY_NEGATIVE)
            return right == ZERO ? POSITIVE : STRICTLY_POSITIVE;
        // Conservative fallback for mixed-sign abstractions.
        return left.negate();
    }
    @Override
    public ValueEnvironment<ExtendedSigns> assumeBinaryExpression(ValueEnvironment<ExtendedSigns> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle) throws SemanticException {

        if(operator instanceof ComparisonLe){
            if(left instanceof Variable && right instanceof Constant) {
                Variable x = (Variable) left;
                Object c = ((Constant) right).getValue();
                if (c instanceof Integer) {
                    int value = (Integer) c;
                    ExtendedSigns bound = value < 0 ? STRICTLY_NEGATIVE : (value == 0 ? NEGATIVE : TOP);
                    ExtendedSigns current = environment.getState(x);
                    return environment.putState(x, current.glb(bound));
                }
            }
        }
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }

    @Override
    public ExtendedSigns evalBinaryExpression(BinaryOperator operator, ExtendedSigns left, ExtendedSigns right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (operator instanceof AdditionOperator) {
            if (left == ZERO) return right;
            if (right == ZERO) return left;
            if(left == TOP || right == TOP) return TOP;
            if(left == BOTTOM || right == BOTTOM) return BOTTOM;
            if (left == NEGATIVE && right == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && right == POSITIVE) return POSITIVE;
            if (left == STRICTLY_NEGATIVE && right == STRICTLY_NEGATIVE) return STRICTLY_NEGATIVE;
            if (left == STRICTLY_POSITIVE && right == STRICTLY_POSITIVE) return STRICTLY_POSITIVE;
            if (left == NEGATIVE && right == STRICTLY_NEGATIVE || left == STRICTLY_NEGATIVE && right == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && right == STRICTLY_POSITIVE || left == STRICTLY_POSITIVE && right == POSITIVE) return POSITIVE;
            return TOP;
        }
        if (operator instanceof SubtractionOperator) {
            ExtendedSigns rightNegated = right.negate();
            if (left == ZERO) return rightNegated;
            if (rightNegated == ZERO) return left;
            if(left == TOP || rightNegated == TOP) return TOP;
            if(left == BOTTOM || rightNegated == BOTTOM) return BOTTOM;
            if (left == NEGATIVE && rightNegated == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && rightNegated == POSITIVE) return POSITIVE;
            if (left == STRICTLY_NEGATIVE && rightNegated == STRICTLY_NEGATIVE) return STRICTLY_NEGATIVE;
            if (left == STRICTLY_POSITIVE && rightNegated == STRICTLY_POSITIVE) return STRICTLY_POSITIVE;
            if (left == NEGATIVE && rightNegated == STRICTLY_NEGATIVE || left == STRICTLY_NEGATIVE && rightNegated == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && rightNegated == STRICTLY_POSITIVE || left == STRICTLY_POSITIVE && rightNegated == POSITIVE) return POSITIVE;
            return TOP;
        }
        if (operator instanceof MultiplicationOperator) {
            if(left == BOTTOM|| right == BOTTOM) return BOTTOM;
            if (left == ZERO || right == ZERO) return ZERO;
            if (left == NEGATIVE) return right.negate();
            if (left == POSITIVE) return right;
            if (left == STRICTLY_NEGATIVE) return right.negate();
            if (left == STRICTLY_POSITIVE) return right;
            return TOP;
        }
        if (operator instanceof DivisionOperator) {
            if (right == ZERO || right== POSITIVE || right == NEGATIVE) return TOP;
            if(left == BOTTOM|| right == BOTTOM) return BOTTOM;
            if (left == ZERO) return ZERO;
            if (left == NEGATIVE) return right.negate();
            if (left == POSITIVE) return right;
            if (left == STRICTLY_NEGATIVE) return right.negate();
            if (left == STRICTLY_POSITIVE) return right;
            return TOP;
        }
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }
}
