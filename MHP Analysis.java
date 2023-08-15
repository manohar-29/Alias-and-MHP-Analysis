package submit_a3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import dont_submit.MhpQuery;
import soot.Local;
import soot.PointsToAnalysis;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;
import soot.util.Chain;


public class MhpAnalysis extends SceneTransformer{
	
	//counter to create threadID;
	int threadCounter=0;

	//list of all methods in program
	List<SootMethod> allMethods;
	
	//obj for peg graph
	PEG peg;
	
	//PointsToAnalysis of soot
	PointsToAnalysis pta;
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your mhp analysis here
		 */
		
		
		pta = Scene.v().getPointsToAnalysis();
		
		//get all classes
        Chain<SootClass> allClasses = Scene.v().getApplicationClasses();
		
        allMethods = new ArrayList<>();
       
        //get all methods 
        for(SootClass c: allClasses) {
        	if(!c.isLibraryClass()) {
	            //get all methods of 'c' class
	            for(SootMethod method: c.getMethods()) {
	                //Ignore constructor
	                if (!method.isConstructor())
	                	allMethods.add(method);
	            }
        	}
        }
        
        peg = new PEG(allMethods); 

        
        SootMethod mainMethod = allMethods.get(0);
		for(SootMethod method: allMethods){
			if(method.isMain())
				mainMethod = method;
		}
		
		String threadId = "Thread-"+ threadCounter++;
		
		
		PEGNode callerOfMain = new PEGNode(null, null, "compiler", "mainCaller");
		
        peg.construct_peg(mainMethod, "main",callerOfMain);
        
        PEGNode beginNodeOfMain = new PEGNode(null, null, "main", "begin");
        
        for(PEGNode n: peg.allBeginNodes) {
        	if(n.threadId.equals("main"))
        		beginNodeOfMain = n;
        }

        
        peg.constructPredGraph();
        
        
        
        Iteration it = new Iteration(peg);
        int flag = 1;
        while(flag == 1) {
        	flag = it.iterate();
        }
        peg.DFS(beginNodeOfMain);
        
        //iterate for queries
	    for(int i=0; i< A3.queryList.size();i++) {
	    	boolean isDataRace = false;
	    	MhpQuery q = A3.queryList.get(i);
	    	String queryVar = q.getVar();
	    	String queryField = q.getField();
	    	
	    	HashMap<QueryNode, HashSet<String>> mhpSet = new HashMap<>();
	    	
	    	for(PEGNode node: peg.graph.keySet()) {
	    		Stmt s = (Stmt)node.unit;
	    		
	    		if(s instanceof DefinitionStmt) {
        			DefinitionStmt ds = (DefinitionStmt) s;
        		
        			Value leftOprd = ds.getLeftOp();
        			Value rightOprd = ds.getRightOp();
        			
        			if(leftOprd instanceof InstanceFieldRef) {
						
						Value baseVar = ((InstanceFieldRef)leftOprd).getBase();
        				SootField baseField = ((InstanceFieldRef)leftOprd).getField();
        				if(queryVar.equals(baseVar.toString())) {
        					if(queryField.equals(baseField.getName().toString())) {
        						QueryNode qn = new QueryNode(node,"write");
        						mhpSet.put(qn, peg.findPointsToList((Local) baseVar));
        						
							}
        				}
        			}
        			else if(rightOprd instanceof InstanceFieldRef) {
						
						Value baseVar = ((InstanceFieldRef)rightOprd).getBase();
        				SootField baseField = ((InstanceFieldRef)rightOprd).getField();
        				if(queryVar.equals(baseVar.toString())) {
        					if(queryField.equals(baseField.getName().toString())) {
        						QueryNode qn = new QueryNode(node,"read");
        						mhpSet.put(qn, peg.findPointsToList((Local) baseVar));
        						
							}
        				}
        			}
	    	
	    		}
	    	}
        	
        	for(QueryNode qnode : mhpSet.keySet()) {
        		for(PEGNode mNode : qnode.node.M) {
        		
        			Stmt s = (Stmt)mNode.unit;
        			
        			if(s instanceof DefinitionStmt) {
            			DefinitionStmt ds = (DefinitionStmt) s;
            		
            			Value leftOprd = ds.getLeftOp();
            			Value rightOprd = ds.getRightOp();
            			
            			if(leftOprd instanceof InstanceFieldRef) {
            				
            				Value baseVar = ((InstanceFieldRef)leftOprd).getBase();
            				SootField baseField = ((InstanceFieldRef)leftOprd).getField();
            				
            				if(queryField.equals(baseField.getName())) {
            					
            					HashSet<String> p2setBaseVar = peg.findPointsToList((Local)baseVar);
            					HashSet<String> p2setQueryVar = mhpSet.get(qnode);
            					
            					if(peg.hasIntersection(p2setBaseVar, p2setQueryVar)) {
            						isDataRace = true;
            						break;
            					}
            				}
            			}
            			
            			else if(rightOprd instanceof InstanceFieldRef) {
            				
            				Value baseVar = ((InstanceFieldRef)rightOprd).getBase();
            				SootField baseField = ((InstanceFieldRef)rightOprd).getField();
            				
            				if(queryField.equals(baseField.getName())) {
            					
            					HashSet<String> p2setBaseVar = peg.findPointsToList((Local)baseVar);
            					HashSet<String> p2setQueryVar = mhpSet.get(qnode);
            					
            					if(peg.hasIntersection(p2setBaseVar, p2setQueryVar) && qnode.access.equals("write")) {
            						isDataRace = true;
            						break;
            					}
            				}
            			}
                	}
        		}
        	}
        	
        	if(isDataRace)
        		A3.answers[i]="Yes";
        	else
        		A3.answers[i] = "No";
        	
        }

        
	}
}	

class QueryNode{
	PEGNode node;
	String access;
	
	QueryNode(PEGNode _node, String _access){
		node = _node;
		access = _access;
	}

}

	

