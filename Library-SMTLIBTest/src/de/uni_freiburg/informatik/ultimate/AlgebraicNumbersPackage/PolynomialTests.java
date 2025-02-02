/*
 * Copyright (C) Tilo Heep
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.AlgebraicNumbersPackage;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import java.util.Arrays;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class PolynomialTests {

    // help functions for tests
    
    private Polynomial createTestPoly(int... a) {
        Rational [] coeff1 = new Rational[a.length];

        for (int i = 0; i < a.length; i++) {
            coeff1[i] = Rational.valueOf(a[i], 1);
        }
        Polynomial res = new Polynomial(coeff1);

        return res;
    }

    private Polynomial createTestPolyRat(Rational... a) {
        Polynomial res = new Polynomial(a);
        return res;
    }

    private BivariatePolynomial createTestBiPoly(Polynomial... a) {
        Rational [][] coeff1 = new Rational[a.length][];

        for (int i = 0; i < a.length; i++) {
            coeff1[i] = a[i].coefficients;
        }
        BivariatePolynomial res = new BivariatePolynomial(coeff1);

        return res;
    }

    private AlgebraicNumbers createTestAlgebraicNumber(int intervalbegin, int intervalend, int... a) {
        Polynomial test = createTestPoly(a);
        Rational intervaldown = Rational.valueOf(intervalbegin, 1);
        Rational intervalup = Rational.valueOf(intervalend, 1);
        AlgebraicNumbers alg = new AlgebraicNumbers(test, intervaldown, intervalup);
        return alg;
    }


    @Test
    public void testRemoveZeros() {

        Polynomial p = createTestPoly(0, 1, 0);
        Polynomial q = createTestPoly(0, 1);
        
        p = p.removeZeros();
        assert(Arrays.equals(q.getCoefficients(), p.getCoefficients()));

        // test if returns empty list if all entries are zero

        p = createTestPoly(0, 0, 0);
        q = createTestPoly();

        p = p.removeZeros();
        assert(Arrays.equals(q.getCoefficients(), p.getCoefficients()));

        // test if returns empty list if there is an empty list

        p = createTestPoly();
        q = createTestPoly();

        q = q.removeZeros();
        assert(Arrays.equals(q.getCoefficients(), p.getCoefficients()));

        // test for multiple zeros

        p = createTestPoly(0, 1, 0, 0, 0);
        q = createTestPoly(0, 1);

        p = p.removeZeros();
        assert(Arrays.equals(q.getCoefficients(), p.getCoefficients()));
    }

    @Test
    public void testgcd() {

        // test if gcd (x**2 + 7x + 6, x + 1) = x + 1

        Polynomial p = createTestPoly(6, 7, 1);
        Polynomial q = createTestPoly(1, 1);
        Polynomial r = createTestPoly(1, 1);

        assert(Arrays.equals(r.getCoefficients(), ManPolys.gcd(p, q).coefficients));

        // test if gcd (x + 1, x + 1) = x + 1
        p = createTestPoly(1, 1);
        q = createTestPoly(1, 1);
        r = createTestPoly(1, 1);

        assert(Arrays.equals(r.getCoefficients(), ManPolys.gcd(p, q).coefficients));

        // test if gcd (x**5 + 2x**4 - x**2 - 1, x**4 - 1) = [] (constant)

        p = createTestPoly(-1, 0, -1, 0, 2, 1);
        q = createTestPoly(-1, 0, 0, 0, 1);
        r = createTestPoly();

        assert(Arrays.equals(r.getCoefficients(), ManPolys.gcd(p, q).coefficients));
    }

    @Test
    public void testLongDivision() {

        // test if x**2 + 7x + 6 / x + 1 = x + 6
        Polynomial p = createTestPoly(6,7,1);
        Polynomial q = createTestPoly(1,1);
        Polynomial r = createTestPoly(6,1);

        assert(Arrays.equals(r.getCoefficients(), ManPolys.longdivision(p, q)[0].coefficients));

        // test if (x + 1) / (x + 1) = 1

        p = createTestPoly(1,1);
        q = createTestPoly(1,1);
        r = createTestPoly(1);

        assert(Arrays.equals(r.getCoefficients(), ManPolys.longdivision(p, q)[0].coefficients));

        // test if x**2 + 2x % 2x + 1 = -3/4

        p = createTestPoly(0,2,1);
        q = createTestPoly(1,2);

        Polynomial [] result = ManPolys.longdivision(p, q);

        Assert.assertEquals(1, result[1].coefficients.length);
        Assert.assertEquals(Rational.valueOf(-3, 4), result[1].coefficients[0]);

        // test if x**4 - 1 mod x**2 + x - 1 = -3x + 1

        p = createTestPoly(-1, 0, 0, 0, 1);
        q = createTestPoly(-1, 1, 1);
        r = createTestPoly(1, -3);
        assert(Arrays.equals(r.getCoefficients(), ManPolys.longdivision(p, q)[1].coefficients));
    }

    @Test
    public void evaluatePoly() {
        Polynomial p = createTestPoly(-1, -1, 0, 1, 1);
        Rational r = Rational.valueOf(21,1);

        Assert.assertEquals(r, p.evaluatePoly(Rational.valueOf(2, 1)));

        p = createTestPoly(20, 0, 1);
        r = Rational.valueOf(20, 1);

        Assert.assertEquals(r, p.evaluatePoly(Rational.ZERO));

        p = createTestPoly(1, 1, 1);
        r = Rational.valueOf(19, 4);

        Assert.assertEquals(r, p.evaluatePoly(Rational.valueOf(3, 2)));
    }

    @Test
    public void testSturmSequence() {
        AlgebraicNumbers a1 = createTestAlgebraicNumber(-2, 2, -1, -1, 0, 1, 1);
        Assert.assertEquals(2, a1.rootsInInterval());

        a1 = createTestAlgebraicNumber(-1, 1, 0, 1, 2, 0, 1);
        Assert.assertEquals(2, a1.rootsInInterval());

        a1 = createTestAlgebraicNumber(-1, 1, 0, 1, 1, 2);
        Assert.assertEquals(1, a1.rootsInInterval());

        a1 = createTestAlgebraicNumber(0, 1, -3, 1, 2);
        Assert.assertEquals(1, a1.rootsInInterval());

        // multiple roots are counted once
        a1 = createTestAlgebraicNumber(0, 1, -1, 2);
        Assert.assertEquals(1, a1.rootsInInterval());

        a1 = createTestAlgebraicNumber(0, 1, -5, 1);
        Assert.assertEquals(0, a1.rootsInInterval());

        a1 = createTestAlgebraicNumber(-1, 6, 0, -120, 274, -225, 85, -15, 1);
        Assert.assertEquals(6, a1.rootsInInterval());
    }

    @Test
    public void testPolynomialAddition() {
        Polynomial p = createTestPoly(-1, -1, 0, 1, 1);
        Polynomial q = createTestPoly();

        Polynomial r = ManPolys.addPolynomials(p, q);
        Assert.assertEquals(r, p);

        p = createTestPoly(0, 1, 1);
        q = createTestPoly(1, 1, 1);

        r = ManPolys.addPolynomials(p, q);
        Polynomial s = createTestPoly(1, 2, 2);
        Assert.assertEquals(r, s);

        p = createTestPoly(0, 0, 0, 1, 4, 8);
        q = createTestPoly(2, 4, 2, 6, 3, 7, 12);

        r = ManPolys.addPolynomials(p, q);
        s = createTestPoly(2, 4, 2, 7, 7, 15, 12);
        Assert.assertEquals(r, s);
    }

    @Test
    public void testLinearMultiply() {
        Polynomial p = createTestPoly(-1, -1, 1, 1);
        Polynomial q = createTestPoly(1, 4);

        Polynomial r = ManPolys.multiplyLinear(p, q);
        Polynomial t = createTestPoly(-1, -5, -3, 5, 4);

        Assert.assertTrue(r.equals(t));
    }

    @Test
    public void testSubxy() {
        Polynomial p = createTestPoly(1);
        BivariatePolynomial a = createTestBiPoly();
        a = BivariatePolynomial.subxy(p);
        System.out.println(Arrays.deepToString(a.coefficients));
    }
    
    @Test
    public void testfactorizePolynomials() {
        AlgebraicNumbers a1 = createTestAlgebraicNumber(-2, 2, 2,1,1,0,1,1);
        System.out.println(a1.toString());
        a1 = a1.makeUnique();
        System.out.println(a1.toString());
    }

    @Test
    public void Countertest() {
        AlgebraicNumbers a1 = createTestAlgebraicNumber(-2, 2, 2,1,1,0,1,1);
        System.out.println(a1.toString());
        System.out.println(a1.makeUnique());
    }

    @Test
    public void testPascaltriangle() {
        System.out.println(BivariatePolynomial.pascaltriangle(7));
    }

    @Test
    public void testfactorize() {
        AlgebraicNumbers a = createTestAlgebraicNumber(25, 49, 2401, 0, -1666, 0, 1);
        Polynomial [] fact = a.factorizePolynomial();
        System.out.println(Arrays.toString(fact[0].coefficients));
    }


    @Test
    public void testMulPoly() {
        Polynomial a = createTestPoly(1,2,2,3,1);
        BivariatePolynomial q = BivariatePolynomial.mulxy(a);
        System.out.println(q.coefficients);
    }
    @Test
    public void testMulPoly2() {
        Polynomial a = createTestPoly(-4, 0, 1);
        BivariatePolynomial q = BivariatePolynomial.mulxy(a);
        System.out.println(q.coefficients);
    }

    // Test Algebraic Division

    @Test
    public void testAlgebraicDivision1() {
        AlgebraicNumbers a = createTestAlgebraicNumber(1,2 ,-3, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 3, -4, 0, 1);

        AlgebraicNumbers c = AlgebraicNumbers.divide(a, b);

        // minimal polynomial of sqrt(3)/sqrt(4)
        Polynomial test = createTestPolyRat(Rational.valueOf(-3, 4), Rational.ZERO,
        Rational.valueOf(1, 1));
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicDivision2() {
        AlgebraicNumbers a = createTestAlgebraicNumber(2,3 ,-3, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 7, -6, 1);

        AlgebraicNumbers c = AlgebraicNumbers.divide(a, b);

        AlgebraicNumbers test = createTestAlgebraicNumber(0, 1, -1, 2);
        Assert.assertEquals(c, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicDivision3() {
        AlgebraicNumbers a = createTestAlgebraicNumber(2,3 ,-3, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(0, 1, -1, 2);
        AlgebraicNumbers c = createTestAlgebraicNumber(4, 6, 50,-20,-3,1);
        AlgebraicNumbers d = createTestAlgebraicNumber(10, 20, -144, 0, 1);

        AlgebraicNumbers z = AlgebraicNumbers.ZERO;

        AlgebraicNumbers aOverb = createTestAlgebraicNumber(5, 6, -6, 1);
        AlgebraicNumbers aOverd = createTestAlgebraicNumber(0, 1, -1, 4);
        AlgebraicNumbers dOverb = createTestAlgebraicNumber(23, 24, -24, 1);
        AlgebraicNumbers dOvera = createTestAlgebraicNumber(3, 4, -4, 1);
        AlgebraicNumbers zeroOverc = AlgebraicNumbers.ZERO;

        Assert.assertEquals(aOverb, AlgebraicNumbers.divide(a, b));
        Assert.assertEquals(aOverd, AlgebraicNumbers.divide(a, d));
        Assert.assertEquals(dOverb, AlgebraicNumbers.divide(d, b));
        Assert.assertEquals(dOvera, AlgebraicNumbers.divide(d, a));
        Assert.assertEquals(zeroOverc, AlgebraicNumbers.divide(z, c));
    }

    // Test algebraic addition

    @Test
    public void testAlgebraicAddition1() {
        // 1/2 + 1/4 = 3/4
        AlgebraicNumbers a = createTestAlgebraicNumber(0,1, -1, 2);
        AlgebraicNumbers b = createTestAlgebraicNumber(0, 1, -1, 4);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        System.out.println(c);
        Assert.assertEquals(Rational.ZERO, c.polynomial.evaluatePoly(Rational.valueOf(3, 4)));

        // 0 + 0 = 0
        a = AlgebraicNumbers.ZERO;
        b = AlgebraicNumbers.ZERO;
        Assert.assertEquals(a, AlgebraicNumbers.add(a,b));

        // a + 0 = 0
        a = createTestAlgebraicNumber(0, 7, -6, 1);
        b = AlgebraicNumbers.ZERO;
        Assert.assertEquals(a, AlgebraicNumbers.add(a, b));

        // 0 + b = 0
        b = createTestAlgebraicNumber(5, 8, -36, 0, 1);
        a = AlgebraicNumbers.ZERO;
        Assert.assertEquals(b, AlgebraicNumbers.add(a, b));
    }

    @Test
    // 1/2 + 1/2 = 1
    public void testAlgebraicAddition2() {
        AlgebraicNumbers a = createTestAlgebraicNumber(0, 1, -1, 2);
        AlgebraicNumbers b = createTestAlgebraicNumber(0, 1, -1, 2);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        Assert.assertEquals(Rational.ZERO, c.polynomial.evaluatePoly(Rational.valueOf(1, 1)));
    }

    @Test
    // 2/8 + 3/8 = 5/8
    public void testAlgebraicAddition3() {
        AlgebraicNumbers a = createTestAlgebraicNumber(0, 1, -2, 8);
        AlgebraicNumbers b = createTestAlgebraicNumber(0, 1, -3, 8);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        Assert.assertEquals(Rational.ZERO, c.polynomial.evaluatePoly(Rational.valueOf(5, 8)));
    }

    @Test
    public void testAlgebraicAddition4() {
        // minpoly (sqrt(2) + sqrt(5)) = x^4 - 14x^2 + 9
        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -2, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 2, -5, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        Polynomial p = createTestPoly(9,0,-14,0,1);
        Assert.assertEquals(p, c.polynomial);

    }
    
    @Test
    public void testAlgebraicAddition5() {
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -14, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(2, 3, -7, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        //Assert.assertEquals(Rational.ZERO, c.polynomial.coefficients);
        //Assert.assertTrue(c.isZero());
        //System.out.println(AlgebraicNumbers.minus(a,b).toString());
        System.out.println(c);
        c = AlgebraicNumbers.multiply(c, c);
        System.out.println(c);

        c = AlgebraicNumbers.multiply(c, c);
        System.out.println(c);
    }

    @Test
    public void testAlgebraicAddition6() {
        AlgebraicNumbers a = createTestAlgebraicNumber(4, 6, 50,-20,-3,1);
        AlgebraicNumbers b = createTestAlgebraicNumber(3, 5, -4, 1);
        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        System.out.println(c);
    }
    @Test
    public void testAlgebraicAddition7() {
        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -3, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 2, -4, 0, 1);
        Polynomial p = createTestPoly(1, -4, 1);
        Assert.assertTrue(p.evaluatePolyAlgebraic(AlgebraicNumbers.add(a,b)).isZero());
    }

    @Test
    public void testAlgebraicAddition8() {
        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -2, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 2, -4, 0, 1);
        Polynomial p = createTestPoly(2, -4, 1);
        System.out.println(p.evaluatePolyAlgebraic(AlgebraicNumbers.add(a,b)).isZero());
    }


    @Test
    public void testAlgebraicAddition9() {
        // -10 + 10 = 0
        AlgebraicNumbers a = createTestAlgebraicNumber(-11, -9, 10, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(9, 11, -100, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.add(a,b);
        Assert.assertTrue(c.isZero());
    }

    @Test
    public void testAlgebraicAddition10() {
        // minpoly (sqrt(3) + 2) = x^2 - 4x + 1
        AlgebraicNumbers a = createTestAlgebraicNumber(-1, 2, -3, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(-2, 2, -2, 1);

        AlgebraicNumbers c = AlgebraicNumbers.add(a, b);
        // minimal polynomial of 2+sqrt(3)
        Polynomial test = createTestPoly(1, -4, 1);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    // Test algebraic multiplication

    @Test
    public void testAlgebraicMultiplication1() {
        // calculate sqrt(6) * 4 = sqrt(96)
        AlgebraicNumbers a = createTestAlgebraicNumber(2, 3, -6, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(3, 4, -4, 1);

        AlgebraicNumbers c = AlgebraicNumbers.multiply(a, b);

        System.out.println(c);
        Polynomial test = createTestPoly(-96, 0, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 2);
        Assert.assertEquals(expect, c);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicMultiplication2() {
        // calculate (3rd-root(7))**3 = 7
        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -7, 0, 0, 1);
        AlgebraicNumbers b = AlgebraicNumbers.multiply(a,a);
        AlgebraicNumbers c = AlgebraicNumbers.multiply(a,b);

        Assert.assertEquals(Rational.ZERO, c.polynomial.evaluatePoly(Rational.valueOf(7, 1)));

        Polynomial test = createTestPoly(-7, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 1);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicMultiplication4() {
        // calculate (3rd-root(7))**3 = 7
        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -7, 0, 0, 1);
        AlgebraicNumbers b = AlgebraicNumbers.multiply(a,a);
        AlgebraicNumbers c = AlgebraicNumbers.multiply(a,b);

        Assert.assertEquals(Rational.ZERO, c.polynomial.evaluatePoly(Rational.valueOf(7, 1)));

        Polynomial test = createTestPoly(-7, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 1);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicMultiplication3() {
        // calculate sqrt(10) * sqrt(10) = 10
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.multiply(a, b);
        
        Polynomial test = createTestPoly(-10, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 1);
        Assert.assertEquals(expect, c);
        Assert.assertTrue(c.rootsInInterval() == 1);
        Assert.assertEquals(c.polynomial, test);
    }

    @Test
    public void testAlgebraicMultiplication5() {

        // Testnumbers
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(2, 3, -8, 0, 1);
        AlgebraicNumbers c = createTestAlgebraicNumber(1, 2, -7, 0, 0, 1);
        AlgebraicNumbers d = createTestAlgebraicNumber(2, 3, -6, 0, 1);
        AlgebraicNumbers e = createTestAlgebraicNumber(3, 4, -4, 1);

        AlgebraicNumbers z = AlgebraicNumbers.ZERO;

        // expected values
        AlgebraicNumbers aTimesb = createTestAlgebraicNumber(8, 9, -80, 0, 1);
        AlgebraicNumbers aTimesd = createTestAlgebraicNumber(7, 8, -60, 0, 1);
        AlgebraicNumbers aTimese = createTestAlgebraicNumber(12, 13, -160, 0, 1);
        AlgebraicNumbers aTimesz = AlgebraicNumbers.ZERO;
        AlgebraicNumbers cTimesc = createTestAlgebraicNumber(3, 4, -49, 0, 0, 1);
        AlgebraicNumbers aSquared = createTestAlgebraicNumber(9, 10, -10, 1);

        // test
        Assert.assertEquals(aTimesb, AlgebraicNumbers.multiply(a, b));
        Assert.assertEquals(aTimesd, AlgebraicNumbers.multiply(a, d));
        Assert.assertEquals(aTimese, AlgebraicNumbers.multiply(a, e));
        Assert.assertEquals(aTimesz, AlgebraicNumbers.multiply(a, z));
        Assert.assertEquals(cTimesc, AlgebraicNumbers.multiply(c, c));
        Assert.assertEquals(aSquared, AlgebraicNumbers.multiply(a, a));
    }

    // Test Subtraction Algebraic

    @Test
    public void testAlgebraicStubtraction() {
        // sqrt(10) - sqrt(8) = sqrt(10)-2sqrt(2)
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(2, 3, -8, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.minus(a, b);
        
        Polynomial test = createTestPoly(4, 0, -36, 0, 1);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicStubtraction2() {
        // 7 - 5 = 2
        AlgebraicNumbers a = createTestAlgebraicNumber(6, 7, -7, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(4, 5, -5, 1);
        AlgebraicNumbers c = AlgebraicNumbers.minus(a, b);
        
        Polynomial test = createTestPoly(-2, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 1);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicStubtraction3() {
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -16, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(1, 2, -4, 0, 1);
        AlgebraicNumbers c = AlgebraicNumbers.minus(a, b);
        
        Polynomial test = createTestPoly(-2, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 1);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);

        a = createTestAlgebraicNumber(4, 5, -17, 0, 1);
        b = createTestAlgebraicNumber(1, 2, -4, 0, 1);
        c = AlgebraicNumbers.minus(a, b);
        
        test = createTestPoly(-13, 4, 1);
        expect = new AlgebraicNumbers(test, 2);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicStubtraction4() {
        AlgebraicNumbers a = createTestAlgebraicNumber(12, 13, 19, -14, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(0, 1, -3, 4, 1);
        AlgebraicNumbers c = AlgebraicNumbers.minus(a, b);
        
        Polynomial test = createTestPoly(1096, -1584, 412, -36, 1);
        AlgebraicNumbers expect = new AlgebraicNumbers(test, 3);
        Assert.assertEquals(expect, c);
        Assert.assertEquals(c.polynomial, test);
        Assert.assertTrue(c.rootsInInterval() == 1);
    }

    @Test
    public void testAlgebraicStubtraction5() {

        // Testnumbers
        AlgebraicNumbers b = createTestAlgebraicNumber(2, 3, -8, 0, 1);
        AlgebraicNumbers c = createTestAlgebraicNumber(1, 2, -7, 0, 0, 1);
        AlgebraicNumbers d = createTestAlgebraicNumber(2, 3, -6, 0, 1);
        AlgebraicNumbers e = createTestAlgebraicNumber(3, 4, -4, 1);

        AlgebraicNumbers z = AlgebraicNumbers.ZERO;

        // expected values
        AlgebraicNumbers minusb = b.negate();
        AlgebraicNumbers eMinusd = createTestAlgebraicNumber(1, 2, 10, -8, 1);
        AlgebraicNumbers cMinusz = c;
        AlgebraicNumbers bMinusd = createTestAlgebraicNumber(0, 1, 4, 0, -28, 0, 1);
        AlgebraicNumbers dMinusc = createTestAlgebraicNumber(0, 2, -167, 252, 108, 14, -18, 0, 1);

        // test
        Assert.assertEquals(minusb, AlgebraicNumbers.minus(z, b));
        Assert.assertEquals(eMinusd, AlgebraicNumbers.minus(e, d));
        Assert.assertEquals(cMinusz, AlgebraicNumbers.minus(c, z));
        Assert.assertEquals(bMinusd, AlgebraicNumbers.minus(b, d));
        Assert.assertEquals(dMinusc, AlgebraicNumbers.minus(d, c));
    }

    @Test
    public void testAlgebraicStubtractionHard() {

        AlgebraicNumbers a = createTestAlgebraicNumber(1, 2, -7, 0, 0, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(2, 3, -6, 0, 1);

        // expected value
        AlgebraicNumbers bMinusa = createTestAlgebraicNumber(0, 2, -167, 252, 108, 14, -18, 0, 1);

        // test
        Assert.assertEquals(bMinusa, AlgebraicNumbers.minus(b, a));
    }


    @Test
    public void testSturmSequence2() {
        AlgebraicNumbers a = createTestAlgebraicNumber(-1, 1, 0,1);
        Rational [] b = new Rational[3];
        b[0] = Rational.valueOf(1, 1);
        b[1] = Rational.valueOf(1, 1);
        b[2] = Rational.ZERO;
        System.out.println(a.SignChangeCounter(b));

        b[0] = Rational.ZERO;
        b[1] = Rational.valueOf(1, 1);
        b[2] = Rational.ZERO;
        System.out.println(a.SignChangeCounter(b));
    }

    @Test
    public void testMulConst() {
        // calculate sqrt(10) * 7 = sqrt(490)
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        Rational b = Rational.valueOf(7, 1);
        a = AlgebraicNumbers.mulConst(a, b);

        Polynomial test = createTestPoly(-490, 0, 1);
        Assert.assertEquals(a.polynomial, test);
    }

    @Test
    public void testEvaluatePolyAlg() {
        // substitute the x in the polynomial x^2-10 with the root of x^2-10
        Polynomial p = createTestPoly(-10, 0, 1);
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        a = p.evaluatePolyAlgebraic(a);
        Assert.assertTrue(a.isZero());
    }

    @Test
    public void testMulConstAlg() {
        // root x = sqrt(10)
        AlgebraicNumbers a = createTestAlgebraicNumber(3, 4, -10, 0, 1);
        a = AlgebraicNumbers.mulConst(a, Rational.valueOf(2, 1));
        a = a.minimize();
        
        // min poly of x = 2*sqrt(10) = sqrt(40)
        Polynomial test = createTestPoly(-40, 0, 1);
        Assert.assertTrue(a.rootsInInterval() == 1);
        Assert.assertEquals(a.polynomial, test);
    }

    @Test
    public void testMinimize() {
        // root x = -10
        AlgebraicNumbers a = createTestAlgebraicNumber(-11, -9, -100, 0, 1);
        a = a.makeUnique();
        Polynomial test = createTestPoly(10, 1);
        Assert.assertTrue(a.rootsInInterval() == 1);
        Assert.assertEquals(a.polynomial, test);
    }

    @Test
    public void testMinimize2() {
        AlgebraicNumbers a = createTestAlgebraicNumber(6, 8, -343, 0, 0, 1);
        a = a.minimize();
        Polynomial test = createTestPoly(-7, 1);
        Assert.assertEquals(a.polynomial, test);
    }

    @Test
    public void testnormalize() {
        AlgebraicNumbers a = createTestAlgebraicNumber(4, 7, -343, 0, 0, 2);
        a = a.makeUnique();
        Assert.assertTrue(a.polynomial.getDegree() == 3);
        Assert.assertTrue(a.numberOfRoot() == 1);
        Assert.assertTrue(a.rootsInInterval() == 1);
    }

    @Test
    public void testLagrangePolyomial2() {
        AlgebraicNumbers a = createTestAlgebraicNumber(6, 8, -343, 0, 0, 1);
        Rational[] nodes = {Rational.ZERO};
        Rational[] values = {Rational.valueOf(1, 1)};
        Polynomial p = a.lagrangePolynomial(nodes, values, 1);
        System.out.println(Arrays.toString(p.coefficients));

        Polynomial test = createTestPoly(1, 1);
        Assert.assertEquals(test, p);
    }

    @Test
    public void testSturmSequence1() {
        AlgebraicNumbers a = createTestAlgebraicNumber(0, 1, -1, -1, 0, 1, 1);
        Assert.assertTrue(!a.SturmsequenceInf()[0].isNegative());
        Assert.assertTrue(!a.SturmsequenceInf()[1].isNegative());
        Assert.assertTrue(!a.SturmsequenceInf()[2].isNegative());
        Assert.assertTrue(a.SturmsequenceInf()[3].isNegative());
        Assert.assertTrue(a.SturmsequenceInf()[4].isNegative());
        System.out.println(a);
        Assert.assertEquals(1, a.rootsInInterval());
    }

    @Test
    public void testSturmSequence3() {
        AlgebraicNumbers a = createTestAlgebraicNumber(6, 8, -7, 1);
        Assert.assertTrue(!a.SturmsequenceInf()[0].isNegative());
        Assert.assertTrue(!a.SturmsequenceInf()[1].isNegative());
        Assert.assertEquals(1, a.rootsInInterval());
    }

    @Test
    public void testEqual() {
        AlgebraicNumbers a = createTestAlgebraicNumber(9, 11, -10, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(9, 12, -100, 0, 1);
        Assert.assertEquals(a, b);
    }

    @Test
    public void testConstructor2() {
        Polynomial p = createTestPoly(-1,-3,0,-3,-4);

        AlgebraicNumbers a = new AlgebraicNumbers(p, 1);
        Assert.assertTrue(a.numberOfRoot() == 1);

        AlgebraicNumbers b = new AlgebraicNumbers(p, 2);
        System.out.println(b);
        Assert.assertTrue(b.numberOfRoot() == 2);

        p = createTestPoly(0,1,2,1);
        a = new AlgebraicNumbers(p, 2);
        Assert.assertTrue(a.numberOfRoot() == 2);

        p = createTestPoly(0,1);
        a = new AlgebraicNumbers(p, 1);
        Assert.assertTrue(a.numberOfRoot() == 1);
    }

    @Test
    public void testEquals() {
        Polynomial p = createTestPoly(1,1,1);
        Polynomial q = createTestPoly(1,1,1);
        Assert.assertTrue(p.equals(q));
    }

    @Test
    public void testEqualsAlgebraic() {
        AlgebraicNumbers a = createTestAlgebraicNumber(10, 11, -11, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(10, 11, -121, 0, 1);
        Assert.assertTrue(b.equals(a));
    }

    @Test
    public void testGreaterAlgebraic() {
        AlgebraicNumbers a = createTestAlgebraicNumber(4, 5, -5, 1);
        AlgebraicNumbers b = createTestAlgebraicNumber(5, 6, -6, 1);
        Assert.assertTrue(b.greater(a));
        Assert.assertTrue(a.smaller(b));

        a = createTestAlgebraicNumber(1, 9, -64, 0, 1);
        b = createTestAlgebraicNumber(1, 9, -49, 0, 1);
        Assert.assertTrue(a.greater(b));
        Assert.assertTrue(b.smaller(a));

        a = createTestAlgebraicNumber(4, 9, -64, 0, 1);
        b = createTestAlgebraicNumber(1, 7, -49, 0, 1);
        Assert.assertTrue(a.greater(b));
        Assert.assertTrue(b.smaller(a));

        a = createTestAlgebraicNumber(-9, -5, -64, 0, 1);
        b = createTestAlgebraicNumber(-9, -1, -49, 0, 1);
        Assert.assertTrue(b.greater(a));
        Assert.assertTrue(a.smaller(b));

        a = createTestAlgebraicNumber(3, 4, -4, 1);
        b = createTestAlgebraicNumber(3, 4, -4, 1);
        Assert.assertTrue(!b.greater(a));
        Assert.assertTrue(!a.smaller(b));
        Assert.assertTrue(a.equals(b));
    }
}
