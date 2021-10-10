/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;

import ompca.Elemental;
import ompca.Octet;
import ompca.vodcg.condition.Relation.Operator;
import ompca.DebugElement;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ReductionOperations 
implements Elemental, Iterable<List<ReductionOperations.ReductionOctet>> {

	static public class ReductionOctet extends 
	Octet<Proposition, String, 
	Function<Proposition, Proposition>, 
	Operator, BiPredicate<Proposition, Proposition>, 
	BiFunction<Proposition, Proposition, Proposition>, 
	BiFunction<Proposition, Proposition, Proposition>, 
	BiFunction<Proposition, List<Proposition>, Proposition>> {

		public ReductionOctet(Operator op, BiPredicate<Proposition, Proposition> tester, 
				BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
				BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
			this(null, null, op, tester, injectTestingTrue, null, reduceOperation);
		}
		
		public ReductionOctet(Operator op, BiPredicate<Proposition, Proposition> tester, 
				BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
				BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
				BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
			this(null, null, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation);
		}
		
		public ReductionOctet(String rule, Operator op, BiPredicate<Proposition, Proposition> tester, 
				BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
				BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
			this(rule, null, op, tester, injectTestingTrue, null, reduceOperation);
		}
		
		public ReductionOctet(String rule, Operator op, BiPredicate<Proposition, Proposition> tester, 
				BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
				BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
				BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
			this(rule, null, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation);
		}
		
		/**
		 * @param rule - TODO? structural reduction rule type with regex support 
		 * 	for automatic reduction compilation
		 * @param probeTestingOp
		 * @param op
		 * @param tester - (ParentProp, SubProp) -> ReduceableCondition,
		 * 	null means no needs to test therefore equals to {@code any -> true}
		 * @param injectTestingTrue - ex. ((A \/ C) /\ B) \/ A = (C /\ B) \/ A 
		 * 	drops A in A \/ C
		 * @param reduceOperation
		 */
		public ReductionOctet(String rule, 
				java.util.function.Function<Proposition, Proposition> probeTestingOp, 
				Operator op, BiPredicate<Proposition, Proposition> tester, 
				BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
				BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
				BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
			super(null, rule, probeTestingOp, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation);
		}

		@Override
		public Object clone() {
			return new ReductionOctet(getPeer2(), getPeer3(), 
					getPeer4(), getPeer5(), getPeer6(), getPeer7(), getPeer8());
		}
		
		
		
		public boolean dropsTestingTrue() {
			BiFunction<Proposition, Proposition, Proposition> inject = getPeer6();
			try {
				return inject == null || inject.apply(null, null) == null;
			} catch (NullPointerException e) {
				return false;
			}
		}

		/**
		 * dropsReduce = isReduced /\ dropsTestingTrue
		 * @return
		 */
		public boolean dropsReduce() {return isReduced() && dropsTestingTrue();}
		
		public boolean isReduced() 										{return getPeer1() != null;}
//		public Proposition setReduced() 								{return setPeer1(true);}
		public Proposition setReduced(Proposition result) 				{return setResult(result);}
		public Proposition setResult(Proposition result) 				{return setPeer1(result);}
		
		public String getRule() 										{return getPeer2();}
		
		public Function<Proposition, Proposition> getProbeTestingOp() 	{return getPeer3();}
		public Operator getOp() 										{return getPeer4();}
		
		public BiPredicate<Proposition, Proposition> getTester()				 		{return getPeer5();}
		public BiFunction<Proposition, Proposition, Proposition> getInjectTestingTrue()	{return getPeer6();}
		public BiFunction<Proposition, Proposition, Proposition> getProbeTestingFalse()	{return getPeer7();}
		
		public BiFunction<Proposition, List<Proposition>, Proposition> 
		getReduceOperation() 											{return getPeer8();}
	}
	
	
	
	private List<List<ReductionOctet>> ros;
	
	final private Map<String, Object> temps = new HashMap<>();
	
	public ReductionOperations() {
		this(new ArrayList<>());
	}
	
	/**
	 * Convenient constructor for disjunctive operations.
	 * @param disjRos
	 */
	public ReductionOperations(ReductionOctet... disjRos) {
		this();
		ros.add(Arrays.asList(disjRos));
	}
	
	/**
	 * @param ros
	 */
	private ReductionOperations(List<List<ReductionOctet>> ros) {
		this.ros = ros;
	}

	
	
	/**
	 * Cloning by resetting.
	 * @param disjRos
	 */
	private boolean addClone(List<ReductionOctet> disjRos) {
		assert disjRos != null;
		List<ReductionOctet> disjClone = new ArrayList<>();
		for (ReductionOctet d : disjRos) {
			if (d == null) DebugElement.throwNullArgumentException("reduction quartet");
			disjClone.add(new ReductionOctet(d.getPeer2(), d.getPeer3(), 
					d.getPeer4(), d.getPeer5(), d.getPeer6(), d.getPeer7(), d.getPeer8()));
		}
		return ros.add(disjClone);
	}

	public boolean add(ReductionOctet... nonDisjunctiveRss) {
		return addAll(Arrays.asList(nonDisjunctiveRss));
	}
	
	public boolean add(Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				null, op, tester, injectTestingTrue, null, reduceOperation));
	}
	
	public boolean add(String rule, Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				rule, op, tester, injectTestingTrue, null, reduceOperation));
	}
	
	public boolean add(String rule, 
			java.util.function.Function<Proposition, Proposition> probeTestingOp, 
			Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				rule, probeTestingOp, op, tester, injectTestingTrue, null, reduceOperation));
	}
	
	public boolean add(Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				null, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation));
	}
	
	public boolean add(String rule, Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				rule, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation));
	}
	
	public boolean add(String rule, 
			java.util.function.Function<Proposition, Proposition> probeTestingOp, 
			Operator op, BiPredicate<Proposition, Proposition> tester, 
			BiFunction<Proposition, Proposition, Proposition> injectTestingTrue, 
			BiFunction<Proposition, Proposition, Proposition> probeTestingFalse, 
			BiFunction<Proposition, List<Proposition>, Proposition> reduceOperation) {
		return add(new ReductionOctet(
				rule, probeTestingOp, op, tester, injectTestingTrue, probeTestingFalse, reduceOperation));
	}

	/**
	 * @param nonDisjunctiveRos
	 */
	public boolean addAll(List<ReductionOctet> nonDisjunctiveRos) {
		if (nonDisjunctiveRos == null || nonDisjunctiveRos.isEmpty()) 
			DebugElement.throwNullArgumentException("non disjunctive reduction operations");
		
		boolean result = true;
		for (ReductionOctet nd : nonDisjunctiveRos) {
			List<ReductionOctet> d = new ArrayList<>();
			result &= d.add((ReductionOctet) nd.clone());
			result &= ros.add(d);
		}
		return result;
	}
	
	/**
	 * @param ro
	 */
	public boolean addPrim(ReductionOctet ro) {
		if (ro == null) DebugElement.throwNullArgumentException("reduction operation");
		
		return add(ro);
	}
	
	/**
	 * @param primDisjRos
	 */
	@SafeVarargs
	final public boolean addPrimDisj(ReductionOctet... primDisjRos) {
		if (primDisjRos == null) DebugElement.throwNullArgumentException("disjunctive ros");
		
		return ros.add(Arrays.asList(primDisjRos));
	}
	

	
	/**
	 * @param roIndex
	 * @return
	 */
	public List<ReductionOctet> getDisjunction(int roIndex) {
		return ros.get(roIndex);
	}
	
//	public Operator getOp(int index) {
//		return ros.get(index).getPeer1();
//	}
		
//	public List<ReduceQuartet> getOperationQuartets(int index) {
//		return ros.get(index).getPeer2();
//	}
	
	
	
	public Proposition getResult(int rosIndex, int roIndex) {
		assert ros != null;
		return ros.get(rosIndex).get(roIndex).getPeer1();
	}

	@SuppressWarnings("unchecked")
	public <T> T getTemp(String key) {
		return (T) temps.get(key);
	}
	
	@SuppressWarnings("unchecked")
	public <T> T setTemp(String key, T value) {
		return (T) temps.put(key, value);
	}
	
	/**
	 * @param rqIndex
	 */
	public Proposition setReduced(int roIndex, Proposition result) throws IndexOutOfBoundsException {
		for (ReductionOctet disjRo : ros.get(roIndex))
			disjRo.setReduced(result);
		return result;
	}

	public Proposition setReduced(int roIndex, int disjIndex, Proposition result) throws IndexOutOfBoundsException {
		return ros.get(roIndex).get(disjIndex).setReduced(result);
	}

	/**
	 * @param roIndex
	 * @return
	 */
	public boolean isReduced(int roIndex) throws IndexOutOfBoundsException {
		for (ReductionOctet disjRo : ros.get(roIndex))
			if (disjRo.isReduced()) return true;
		return false;
	}
	
	public boolean isReduced(int roIndex, int disjIndex) throws IndexOutOfBoundsException {
		return ros.get(roIndex).get(disjIndex).isReduced();
	}
	

	
	/**
	 * @return
	 */
	public boolean isEmpty() {
		assert ros != null;
		return ros.isEmpty();
	}

	

	/* (non-Javadoc)
	 * @see java.lang.Iterable#iterator()
	 */
	@Override
	public Iterator<List<ReductionOctet>> iterator() {
		assert ros != null;
		return ros.iterator();
	}

	
	
	public void clear() {
		assert ros != null;
		ros.clear();
	}

	
	
	/**
	 * @return
	 */
	public int size() {
		assert ros != null;
		return ros.size();
	}

	/**
	 * @param from
	 * @param to
	 * @return
	 */
	public ReductionOperations subList(int from, int to) {
		try {
			return new ReductionOperations(ros.subList(from, to));
		} catch (IndexOutOfBoundsException e) {
//			VOPCondGen.throwNullArgumentException(new Integer[] {from, to});
			return null;
		}
	}

	/**
	 * @param reducesRecursively
	 * @return
	 */
	public ReductionOperations shiftReduce(boolean reducesRecursively) {
		ReductionOperations sr = subList(1, size());
		// independent RO for each adding, each RO has it's own boolean flags
		if (reducesRecursively) sr.addClone(ros.get(0));
		return sr;
	}
	
	
	
	public String toString() {
		return ros.toString();
	}

}