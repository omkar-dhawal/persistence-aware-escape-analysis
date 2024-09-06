/**
 * Copyright (C) 2013 Rohan Padhye
 * 
 * This library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as 
 * published by the Free Software Foundation, either version 2.1 of the 
 * License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package vasco.callgraph;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Map;
import soot.SceneTransformer;

/**
 * A Soot {@link SceneTransformer} for performing {@link PointsToAnalysis}.
 * 
 * @author Rohan Padhye
 */
public class CallGraphTransformer extends SceneTransformer {
	
	private PointsToAnalysis pointsToAnalysis;
	public static HashSet<String> safeMethod = new HashSet<>();
	public static HashSet<String> safeArgMethod = new HashSet<>();
	
	
	CallGraphTransformer(String safeDirectory, String safeArgDirectory){
		try (BufferedReader br = new BufferedReader(new FileReader(safeDirectory + "/safe.txt"))) {
			String line;
	        // Read the file line by line
	        while ((line = br.readLine()) != null) {
	        // Trim trailing spaces from the line and add it to the HashSet
	        	safeMethod.add(line.trim());
	        }
	    } catch (IOException e) {
	            // Handle the exception
	    	e.printStackTrace();
	    }
		try (BufferedReader br = new BufferedReader(new FileReader(safeArgDirectory + "/safeArg.txt"))) {
			String line;
	        // Read the file line by line
	        while ((line = br.readLine()) != null) {
	        // Trim trailing spaces from the line and add it to the HashSet
	        	safeArgMethod.add(line.trim());
	        }
	    } catch (IOException e) {
	            // Handle the exception
	    	e.printStackTrace();
	    }
	}

	/**
	 * {@inheritDoc}
	 */
	@SuppressWarnings("deprecation")
	@Override
	protected void internalTransform(String arg0, @SuppressWarnings("rawtypes") Map arg1) {
		// Perform the points-to analysis
		pointsToAnalysis = new PointsToAnalysis();
		pointsToAnalysis.doAnalysis();
		
	}
	
	/**
	 * Returns a reference to the {@link PointsToAnalysis} object. 
	 * @return a reference to the {@link PointsToAnalysis} object
	 */
	public PointsToAnalysis getPointsToAnalysis() {
		return pointsToAnalysis;
	}

	
	
}
