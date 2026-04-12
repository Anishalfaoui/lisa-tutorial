package it.unive.lisa.tutorial;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.UnaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.util.datastructures.regex.TopAtom;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class TwoVariablesInequality 	
		
		implements ValueDomain<TwoVariablesInequality> {
        private static final double EPSILON = 1e-9;
    private static final int MAX_CLOSURE_FIXPOINT_ITERATIONS = 8;
    public static final TwoVariablesInequality TOP = new TwoVariablesInequality(true);
    public static final TwoVariablesInequality BOTTOM = new TwoVariablesInequality(false);
    private final boolean top;
    private final boolean bottom;
    private final Set<LinearInequality> inequalities;

    private Set<LinearInequality> immutableConstraintSet(Set<LinearInequality> constraints) {
        if (constraints.isEmpty())
            return Collections.emptySet();
        return Collections.unmodifiableSet(new HashSet<>(constraints));
    }

    private TwoVariablesInequality(boolean top) {
		this.top = top;
		this.bottom = !top;
        this.inequalities = Collections.emptySet();
	}
    public TwoVariablesInequality(Set<LinearInequality>inequalities) {
        Set<LinearInequality> normalized = removeDuplicates(inequalities);
        if (hasContradiction(normalized)) {
            this.top = false;
            this.bottom = true;
            this.inequalities = Collections.emptySet();
            return;
        }

        this.top = normalized.isEmpty();
        this.bottom = false;
        this.inequalities = immutableConstraintSet(normalized);
	}


    public TwoVariablesInequality top() {
        return TOP;
    }
    public boolean isTop(){
        return this.top;
    }
    public boolean isBottom(){
        return this.bottom;
    }

    public TwoVariablesInequality bottom() {
        return BOTTOM;
    }

    public boolean knowsIdentifier(Identifier identifier) {
        return vars().contains(identifier);
    }
    public TwoVariablesInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        TwoVariablesInequality result = this;
        for (Identifier id : new HashSet<>(vars()))
            if (predicate.test(id))
                result = result.forgetIdentifier(id);
        return result;
    }
    public TwoVariablesInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    public StructuredRepresentation representation() {
        if(isTop())
            return new StringRepresentation("TOP");
        if(isBottom())
            return new StringRepresentation("BOTTOM");
        return new StringRepresentation(toString());
    }

    private String coefficientsKey(LinearInequality ineq) {
        List<String> terms = new ArrayList<>();
        for (Map.Entry<Identifier, Double> entry : ineq.coefficients.entrySet())
            terms.add(entry.getKey().getName() + ":" + entry.getValue());
        Collections.sort(terms);
        return String.join(";", terms);
    }

    private boolean isProportional(Map<Identifier, Double> lhs, Map<Identifier, Double> rhs) {
        if (lhs.size() != rhs.size())
            return false;
        Double ratio = null;
        for (Map.Entry<Identifier, Double> entry : lhs.entrySet()) {
            Double rightCoef = rhs.get(entry.getKey());
            if (rightCoef == null)
                return false;
            if (Math.abs(rightCoef) < 1e-9)
                return false;
            double currentRatio = entry.getValue() / rightCoef;
            if (currentRatio <= 0)
                return false;
            if (ratio == null)
                ratio = currentRatio;
            else if (Math.abs(ratio - currentRatio) > 1e-9)
                return false;
        }
        return ratio != null;
    }

    private boolean implies(LinearInequality stronger, LinearInequality weaker) {
        if (stronger.coefficients.equals(weaker.coefficients))
            return stronger.constant <= weaker.constant;

        if (!isProportional(stronger.coefficients, weaker.coefficients))
            return false;

        Identifier first = weaker.coefficients.keySet().iterator().next();
        double scale = stronger.coefficients.get(first) / weaker.coefficients.get(first);
        return stronger.constant <= scale * weaker.constant + 1e-9;
    }

    private boolean isEntailedBy(LinearInequality target, Set<LinearInequality> constraints) {
        for (LinearInequality candidate : constraints)
            if (implies(candidate, target))
                return true;
        return false;
    }

    private LinearInequality normalizeInequality(LinearInequality inequality) {
        if (inequality == null)
            return null;

        Map<Identifier, Double> cleanedCoefficients = new HashMap<>();
        for (Map.Entry<Identifier, Double> entry : inequality.coefficients.entrySet())
            if (Math.abs(entry.getValue()) > EPSILON)
                cleanedCoefficients.put(entry.getKey(), entry.getValue());

        return new LinearInequality(cleanedCoefficients, inequality.constant, inequality.lessOrEqual);
    }

    private boolean isContradictoryZeroConstraint(LinearInequality inequality) {
        if (!inequality.coefficients.isEmpty())
            return false;

        if (inequality.lessOrEqual)
            return inequality.constant < -EPSILON;

        return inequality.constant <= EPSILON;
    }

    private boolean isAlwaysTrueZeroConstraint(LinearInequality inequality) {
        if (!inequality.coefficients.isEmpty())
            return false;

        if (inequality.lessOrEqual)
            return inequality.constant >= -EPSILON;

        return inequality.constant > EPSILON;
    }

    private boolean hasContradiction(Set<LinearInequality> constraints) {
        for (LinearInequality inequality : constraints) {
            LinearInequality normalized = normalizeInequality(inequality);
            if (normalized != null && isContradictoryZeroConstraint(normalized))
                return true;
        }
        return false;
    }

    private Set<LinearInequality> commonUpperBoundConstraints(
            Set<LinearInequality> leftConstraints,
            Set<LinearInequality> rightConstraints) {
        Set<LinearInequality> candidates = new HashSet<>(leftConstraints);
        candidates.addAll(rightConstraints);

        Set<LinearInequality> common = new HashSet<>();
        for (LinearInequality candidate : candidates)
            if (isEntailedBy(candidate, leftConstraints) && isEntailedBy(candidate, rightConstraints))
                common.add(candidate);

        return common;
    }

    private TwoVariablesInequality withAddedInequality(LinearInequality inequality) {
        if (isBottom() || inequality == null)
            return this;
        Set<LinearInequality> updated = new HashSet<>(inequalities);
        updated.add(inequality);
        Set<LinearInequality> closed = closureGlb(removeDuplicates(updated));
        if (hasContradiction(closed))
            return BOTTOM;
        return new TwoVariablesInequality(closed);
    }

    private static class LinearForm {
        private final Map<Identifier, Double> coefficients;
        private final double constant;
        private final boolean supported;

        private LinearForm(Map<Identifier, Double> coefficients, double constant, boolean supported) {
            this.coefficients = coefficients;
            this.constant = constant;
            this.supported = supported;
        }
    }

    private LinearForm unsupportedLinearForm() {
        return new LinearForm(new HashMap<>(), 0.0, false);
    }

    private LinearForm constantLinearForm(double constant) {
        return new LinearForm(new HashMap<>(), constant, true);
    }

    private LinearForm identifierLinearForm(Identifier identifier) {
        Map<Identifier, Double> coefficients = new HashMap<>();
        coefficients.put(identifier, 1.0);
        return new LinearForm(coefficients, 0.0, true);
    }

    private LinearForm combineLinearForms(LinearForm left, LinearForm right, double rightScale) {
        if (!left.supported || !right.supported)
            return unsupportedLinearForm();

        Map<Identifier, Double> coefficients = new HashMap<>(left.coefficients);
        for (Map.Entry<Identifier, Double> entry : right.coefficients.entrySet())
            coefficients.merge(entry.getKey(), rightScale * entry.getValue(), Double::sum);

        return new LinearForm(coefficients, left.constant + rightScale * right.constant, true);
    }

    private LinearForm scaleLinearForm(LinearForm form, double scale) {
        if (!form.supported)
            return unsupportedLinearForm();

        Map<Identifier, Double> coefficients = new HashMap<>();
        for (Map.Entry<Identifier, Double> entry : form.coefficients.entrySet())
            coefficients.put(entry.getKey(), entry.getValue() * scale);

        return new LinearForm(coefficients, form.constant * scale, true);
    }

    private Double numericConstant(SymbolicExpression expression) {
        if (!(expression instanceof Constant))
            return null;

        Object value = ((Constant) expression).getValue();
        if (!(value instanceof Integer))
            return null;

        return ((Integer) value).doubleValue();
    }

    private LinearForm parseLinearForm(SymbolicExpression expression) {
        if (expression instanceof Identifier)
            return identifierLinearForm((Identifier) expression);

        Double constant = numericConstant(expression);
        if (constant != null)
            return constantLinearForm(constant);

        if (expression instanceof UnaryExpression) {
            UnaryExpression unaryExpression = (UnaryExpression) expression;
            if (unaryExpression.getOperator() instanceof NumericNegation)
                return scaleLinearForm(parseLinearForm(unaryExpression.getExpression()), -1.0);

            return unsupportedLinearForm();
        }

        if (!(expression instanceof BinaryExpression))
            return unsupportedLinearForm();

        BinaryExpression binaryExpression = (BinaryExpression) expression;
        SymbolicExpression left = binaryExpression.getLeft();
        SymbolicExpression right = binaryExpression.getRight();

        if (binaryExpression.getOperator() instanceof AdditionOperator)
            return combineLinearForms(parseLinearForm(left), parseLinearForm(right), 1.0);

        if (binaryExpression.getOperator() instanceof SubtractionOperator)
            return combineLinearForms(parseLinearForm(left), parseLinearForm(right), -1.0);

        if (binaryExpression.getOperator() instanceof MultiplicationOperator) {
            Double leftConstant = numericConstant(left);
            if (leftConstant != null)
                return scaleLinearForm(parseLinearForm(right), leftConstant);

            Double rightConstant = numericConstant(right);
            if (rightConstant != null)
                return scaleLinearForm(parseLinearForm(left), rightConstant);
        }

        return unsupportedLinearForm();
    }

    private LinearInequality parseLeq(ValueExpression expression) {
        if (!(expression instanceof BinaryExpression))
            return null;

        BinaryExpression binaryExpression = (BinaryExpression) expression;
        if (!(binaryExpression.getOperator() instanceof ComparisonLe))
            return null;

        LinearForm left = parseLinearForm(binaryExpression.getLeft());
        LinearForm right = parseLinearForm(binaryExpression.getRight());
        if (!left.supported || !right.supported)
            return null;

        Map<Identifier, Double> coefficients = new HashMap<>(left.coefficients);
        for (Map.Entry<Identifier, Double> entry : right.coefficients.entrySet())
            coefficients.merge(entry.getKey(), -entry.getValue(), Double::sum);

        LinearInequality parsed = normalizeInequality(new LinearInequality(coefficients, right.constant - left.constant));
        if (parsed == null)
            return null;

        if (parsed.coefficients.size() > 2)
            return null;

        return parsed;
    }

    @Override
    public TwoVariablesInequality assume(
        ValueExpression expression,
        ProgramPoint src,
        ProgramPoint dest,
        SemanticOracle oracle) throws SemanticException {
        if (isBottom())
            return this;

        LinearInequality inequality = parseLeq(expression);
        return withAddedInequality(inequality);
    }
    public static boolean isSpecialIdentifier(Identifier id) {
        return id.toString().contains("heap") || id.toString().contains("this") || id.toString().contains("&pp@");
    }
    public TwoVariablesInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint pp,
        SemanticOracle oracle) throws SemanticException {
        if(isSpecialIdentifier(identifier))
            return this;

        TwoVariablesInequality strongUpdated = forgetIdentifier(identifier);

        if(valueExpression instanceof Identifier){
            Identifier id = (Identifier) valueExpression;
            Map<Identifier, Double> coefficients = new HashMap<>();
            coefficients.put(identifier, 1.0);
            coefficients.put(id, -1.0);
            LinearInequality inequality = new LinearInequality(coefficients, 0.0);
            return strongUpdated.withAddedInequality(inequality);
        }
        if(valueExpression instanceof Constant){
            Constant c = (Constant) valueExpression;
            if (!(c.getValue() instanceof Integer))
                return strongUpdated;
            Map<Identifier, Double> coefficients = new HashMap<>();
            coefficients.put(identifier, 1.0);
            LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
            Map<Identifier, Double> reverse = new HashMap<>();
            reverse.put(identifier, -1.0);
            LinearInequality dual = new LinearInequality(reverse, -((Integer) c.getValue()));
            return strongUpdated.withAddedInequality(inequality).withAddedInequality(dual);
        }
        if(valueExpression instanceof BinaryExpression){
            BinaryExpression binaryExpression = (BinaryExpression) valueExpression;
            // On veut que la forme soit x = y + c 
            if(binaryExpression.getOperator() instanceof AdditionOperator && binaryExpression.getLeft() instanceof Identifier && binaryExpression.getRight() instanceof Constant){
                // On veut que la forme soit x = y + c => soit transformé vers 
                // create the form for  x - y <= c
                Identifier y = (Identifier) binaryExpression.getLeft();
                Constant c = (Constant) binaryExpression.getRight();
                Map<Identifier, Double> coefficients = new HashMap<>();
                coefficients.put(identifier, 1.0);
                coefficients.put(y, -1.0);
                LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
                Map<Identifier, Double> reverse = new HashMap<>();
                reverse.put(y, 1.0);
                reverse.put(identifier, -1.0);
                LinearInequality dual = new LinearInequality(reverse, -((Integer) c.getValue()));
                return strongUpdated.withAddedInequality(inequality).withAddedInequality(dual);
            }
            // handle the case of x = b*y + c
            if(binaryExpression.getOperator() instanceof AdditionOperator &&  binaryExpression.getRight() instanceof Constant){
                if((binaryExpression.getLeft() instanceof BinaryExpression)){
                    BinaryExpression leftExpr = (BinaryExpression) binaryExpression.getLeft();
                    if((leftExpr.getOperator() instanceof MultiplicationOperator) && leftExpr.getLeft() instanceof Constant && leftExpr.getRight() instanceof Identifier){
                        // On veut que la forme soit x = b*y + c => soit transformé vers 
                        // create the form for  x - b*y <= c
                        Constant b = (Constant) leftExpr.getLeft();
                        Identifier y = (Identifier) leftExpr.getRight();
                        Constant c = (Constant) binaryExpression.getRight();
                        if (!(b.getValue() instanceof Integer) || !(c.getValue() instanceof Integer))
                            return strongUpdated;
                        Map<Identifier, Double> coefficients = new HashMap<>();
                        coefficients.put(identifier, 1.0);
                        coefficients.put(y, -((Integer)b.getValue()).doubleValue());
                        LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
                        return strongUpdated.withAddedInequality(inequality);
                    }
                }
                
                
            
            }
        }
        return strongUpdated;
    }

    public Set<LinearInequality> removeDuplicates(Set<LinearInequality> inequalities) {
        // GO TRHOW the inequalities and remove the equivalent ones 
        Set<LinearInequality> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            LinearInequality normalized = normalizeInequality(inequality);
            if (normalized == null)
                continue;

            if (isAlwaysTrueZeroConstraint(normalized))
                continue;

            result.add(normalized);
        }
        return result;
    }

    private Set<LinearInequality> closureFixpoint(Set<LinearInequality> inequalities, boolean glbClosure) {
        Set<LinearInequality> current = removeDuplicates(new HashSet<>(inequalities));
        current = glbClosure ? glbLinearInequality(current) : lubLinearInequality(current);

        for (int iteration = 0; iteration < MAX_CLOSURE_FIXPOINT_ITERATIONS; iteration++) {
            Set<LinearInequality> expanded = new HashSet<>(current);
            expanded.addAll(transitivity(current));
            expanded = removeDuplicates(expanded);
            Set<LinearInequality> next = glbClosure ? glbLinearInequality(expanded) : lubLinearInequality(expanded);
            if (next.equals(current))
                return next;
            current = next;
        }

        return current;
    }

    public Set<LinearInequality> closureLub(Set<LinearInequality> inequalities) {
        return closureFixpoint(inequalities, false);
    }
    public Set<LinearInequality> closureGlb(Set<LinearInequality> inequalities) {
        return closureFixpoint(inequalities, true);
    }
    public Set<LinearInequality> transitivity(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> newInequalities = new HashSet<>();
        for (LinearInequality ineq1 : inequalities) {
            for (LinearInequality ineq2 : inequalities) {
                if (ineq1.equals(ineq2)) continue;
                // Trouver des variables communes entre les deux inégalités
                Set<Identifier> commonVars = new HashSet<>(ineq1.var());
                commonVars.retainAll(ineq2.var());
                if (!commonVars.isEmpty()) {
                    // Pour chaque variable commune, essayer de dériver une nouvelle inégalité
                    for (Identifier commonVar : commonVars) {
                        Double coef1 = ineq1.coefficients.get(commonVar);
                        Double coef2 = ineq2.coefficients.get(commonVar);
                        boolean hasDifferentSign = coef1 * coef2 < 0;
                        // Vérifier si les coefficients ont le même signe
                        if (hasDifferentSign ) {
                            // Créer une nouvelle inégalité combinée
                            Map<Identifier, Double> newCoeffs = new HashMap<>();
                            double scale1 = Math.abs(coef2);
                            double scale2 = Math.abs(coef1);
                            // Ajouter les coefficients mis à l'échelle de la première inégalité
                            for (Map.Entry<Identifier, Double> entry : ineq1.coefficients.entrySet()) {
                                Identifier var = entry.getKey();
                                if (!var.equals(commonVar)) {
                                    newCoeffs.put(var, entry.getValue() * scale1);
                                }
                            }
                            // Ajouter les coefficients mis à l'échelle de la seconde inégalité
                            for (Map.Entry<Identifier, Double> entry : ineq2.coefficients.entrySet()) {
                                Identifier var = entry.getKey();
                                if (!var.equals(commonVar)) {
                                    double existingCoef = newCoeffs.getOrDefault(var, 0.0);
                                    newCoeffs.put(var, existingCoef + entry.getValue() * scale2);
                                }
                            }
                            
                            // Calculer la nouvelle constante
                            double newConstant = ineq1.constant * scale1 + ineq2.constant * scale2;
                            
                            // Créer la nouvelle inégalité et l'ajouter aux résultats
                            LinearInequality newIneq = new LinearInequality(newCoeffs, newConstant);
                            newInequalities.add(newIneq);
                        }
                    }
                }
            }
        }
        return newInequalities;
       
    }
    /*
     * 
     * * Implémente l'opérateur de jointure lub pour les inégalités linaires 
     * e.g: ax + by <= c et ax + by <= d => ax + by <= min(c,d) e.g : 
     */
    public Set<LinearInequality> lubLinearInequality(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> result = new HashSet<>(inequalities);
        // Étape 1: Supprimer les inégalités redondantes (même coefficient, constante différente)
        Map<String, LinearInequality> coeffToIneq = new HashMap<>();
        // Regrouper par coefficients et garder seulement l'inégalité la plus restrictive
        // exemple si tu sais que x <= 5 et x <= 10, tu gardes x <= 5 
        for (LinearInequality ineq : result) {
            String key = coefficientsKey(ineq);
            // Conserver seulement l'inégalité avec la plus grande constante
            if (!coeffToIneq.containsKey(key) || coeffToIneq.get(key).constant <= ineq.constant) {
                coeffToIneq.put(key, ineq);
            }
        }
        return new HashSet<>(coeffToIneq.values());
    }
    public Set<LinearInequality> glbLinearInequality(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> result = new HashSet<>(inequalities);
        // Étape 1: Supprimer les inégalités redondantes (même coefficient, constante différente)
        Map<String, LinearInequality> coeffToIneq = new HashMap<>();
        // Regrouper par coefficients et garder seulement l'inégalité la plus restrictive
        // exemple si tu sais que x <= 5 et x <= 10, tu gardes x <= 5 
        for (LinearInequality ineq : result) {
            String key = coefficientsKey(ineq);
            // Conserver seulement l'inégalité avec la plus grande constante
            if (!coeffToIneq.containsKey(key) || coeffToIneq.get(key).constant > ineq.constant) {
                coeffToIneq.put(key, ineq);
            }
        }
        return new HashSet<>(coeffToIneq.values());
    }
    public TwoVariablesInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        // Handle different types of expressions
        return this;
    }
    @Override
    public boolean lessOrEqual(TwoVariablesInequality other) throws SemanticException {
        if (isBottom())
            return true;
        if (other.isBottom())
            return false;
        if (other.isTop())
            return true;
        if (isTop())
            return false;

        Set<LinearInequality> thisClosed = closureGlb(removeDuplicates(new HashSet<>(inequalities)));
        Set<LinearInequality> otherClosed = closureGlb(removeDuplicates(new HashSet<>(other.inequalities)));
        for (LinearInequality target : otherClosed)
            if (!isEntailedBy(target, thisClosed))
                return false;
        return true;
    }
    @Override
    public TwoVariablesInequality lub(TwoVariablesInequality other) throws SemanticException {
        // Keep only constraints that are entailed by both operands.
        if(isTop() || other.isTop())
            return TOP;
        if(isBottom())
            return other;
        if(other.isBottom())
            return this;

        Set<LinearInequality> thisClosed = closureGlb(removeDuplicates(new HashSet<>(this.inequalities)));
        Set<LinearInequality> otherClosed = closureGlb(removeDuplicates(new HashSet<>(other.inequalities)));
        Set<LinearInequality> commonUpperBound = commonUpperBoundConstraints(thisClosed, otherClosed);
        if (commonUpperBound.isEmpty())
            return TOP;

        return new TwoVariablesInequality(closureLub(removeDuplicates(commonUpperBound)));
    }
    @Override
    public TwoVariablesInequality glb(TwoVariablesInequality other) throws SemanticException {
        if (isTop()) return other;
        if (other.isTop()) return this;
        if (isBottom() || other.isBottom()) return BOTTOM;
        Set<LinearInequality> result = new HashSet<>(this.inequalities);
        result.addAll(other.inequalities);
        return new TwoVariablesInequality(closureGlb(removeDuplicates(result)));
    }

    
    public Set<Identifier> vars() {
        Set<Identifier> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            result.addAll(inequality.var());
        }
        return result;
    }
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        boolean first = true;
        
        for(LinearInequality inequality : inequalities) {
            if(!first)
                sb.append(", ");
            sb.append(inequality.toString());
            first = false;
        }
        sb.append("}");
        return sb.toString();
    }


     /**
     * Implémente l'opérateur de restriction πY défini dans l'article
     * πY(T) = {t ∈ T | var(t) ⊆ Y}
     */
    public Set<LinearInequality> restrictTo(Set<Identifier> variables) {
        Set<LinearInequality> restricted = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            if (variables.containsAll(inequality.var())) {
                restricted.add(inequality);
            }
        }
        return restricted;
    }
    /**
     * Classe représentant une inégalité linéaire ax + by ≤ c
    */
    public static final class LinearInequality {
        // Coefficients des variables (ax + by)
        private final Map<Identifier, Double> coefficients;
        private final boolean lessOrEqual;
        // Constante c dans ax + by ≤ c
        private final double constant;

        public LinearInequality(Map<Identifier, Double> coefficients, double constant) {
            this(coefficients, constant, true);
        }
        public LinearInequality(Map<Identifier, Double> coefficients, double constant, boolean lessOrEqual) {
            this.coefficients = Collections.unmodifiableMap(new HashMap<>(coefficients));
            this.constant = constant;
            this.lessOrEqual = lessOrEqual;
        }

        public Map<Identifier, Double> getCoefficients() {
            return coefficients;
        }

        public double getConstant() {
            return constant;
        }

        public boolean isLessOrEqual() {
            return lessOrEqual;
        }

        public boolean isEqualCoefficients(LinearInequality other) {
            return this.coefficients.equals(other.coefficients);
        }
      
        /**
         * Implémente la fonction var(ax + by ≤ c) comme définie dans l'article
         */
        public Set<Identifier> var() {
            Set<Identifier> result = new HashSet<>();
            for (Map.Entry<Identifier, Double> entry : coefficients.entrySet()) {
                double coef = entry.getValue();
                if(coef != 0)
                    result.add(entry.getKey());
            }
            return result;
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (!(obj instanceof LinearInequality))
                return false;
            LinearInequality other = (LinearInequality) obj;
            return coefficients.equals(other.coefficients) && Double.compare(constant, other.constant) == 0
                    && lessOrEqual == other.lessOrEqual;
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(coefficients, constant, lessOrEqual);
        }
     

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            boolean first = true;

            List<Map.Entry<Identifier, Double>> entries = new ArrayList<>(coefficients.entrySet());
            entries.sort((a, b) -> a.getKey().getName().compareTo(b.getKey().getName()));
            for (Map.Entry<Identifier, Double> entry : entries) {
                double coef = entry.getValue();
                if (!first && coef > 0) sb.append(" + ");
                else if (!first) sb.append(" - ");
                else if (coef < 0) sb.append("-");
                
                if (Math.abs(Math.abs(coef) - 1.0) > 0.0001) {
                    sb.append(Math.abs(coef)).append("*");
                }
                
                sb.append(entry.getKey().getName());
                first = false;
            }
            if(lessOrEqual)
                sb.append(" <= ");
            else
                sb.append(" < ");
            sb.append(constant);
            return sb.toString();
        }
    }


    public TwoVariablesInequality close() {
        if (isTop() || isBottom())
            return this;
        return new TwoVariablesInequality(closureGlb(removeDuplicates(new HashSet<>(inequalities))));
    }
    public TwoVariablesInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        if (isTop() || isBottom())
            return this;

        Set<LinearInequality> filtered = new HashSet<>();
        for (LinearInequality inequality : inequalities)
            if (!inequality.var().contains(identifier))
                filtered.add(inequality);

        return filtered.isEmpty() ? TOP : new TwoVariablesInequality(closureGlb(removeDuplicates(filtered)));
    }

    public Satisfiability satisfies(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        if (isBottom())
            return Satisfiability.BOTTOM;
        if (isTop())
            return Satisfiability.UNKNOWN;

        LinearInequality queried = parseLeq(expression);
        if (queried == null)
            return Satisfiability.UNKNOWN;

        Set<LinearInequality> closed = closureGlb(removeDuplicates(new HashSet<>(inequalities)));
        if (isEntailedBy(queried, closed))
            return Satisfiability.SATISFIED;
        return Satisfiability.UNKNOWN;
    }




}
