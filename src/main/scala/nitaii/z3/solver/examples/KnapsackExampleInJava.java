package nitaii.z3.solver.examples;

import nitaii.z3.solver.npsolvers.Knapsack;

public class KnapsackExampleInJava {
	
	public static void main(String[] args) {
		double[] weights = new double[]{1,2,2,2,8};
		double[] values = new double[]{5,1,1.5,1.5,7};
		double capacity = 13;
		Knapsack knap = new Knapsack(weights, values, capacity);
		
		
		System.out.println("vector solution:");
		for(int x : knap.getSolution())
			System.out.println(x);
		
		System.out.println("value:");
		System.out.println(knap.getValue());
		
	}

}
