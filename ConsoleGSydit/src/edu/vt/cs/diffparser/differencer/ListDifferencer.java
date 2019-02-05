package edu.vt.cs.diffparser.differencer;

import java.util.ArrayList;
import java.util.List;

import edu.vt.cs.diffparser.astdiff.CommonADT;

public abstract class ListDifferencer<T> extends Differencer<List<T>> {
	
	abstract protected boolean isMatched(T left, T right);
	
	public List<CommonADT<T>> findLongestCommonSubsequence(List<T> left, List<T> right) {
		int m = left.size();
		int n = right.size();
		
		int[][] c = new int[m+1][n+1];
		int[][] b = new int[m+1][n+1];
		
		for(int i = 0; i <=m; i++){
			c[i][0] = 0;
			b[i][0] = 0;		
		}
		for(int i = 0; i <= n; i ++){
			c[0][i] = 0;
			b[0][i] = 0;
		}
		for(int i = 1; i <= m; i ++){
			for(int j = 1; j <= n; j++){
				if (isMatched(left.get(i-1), right.get(j-1))) {
					c[i][j]= c[i-1][j-1] + 1;
					b[i][j] = DIAG;
				} else if(c[i-1][j] >= c[i][j-1]) {
					c[i][j] = c[i-1][j];
					b[i][j] = UP;
				} else {
					c[i][j] = c[i][j-1];
					b[i][j] = LEFT;
				}
			}
		}
		
		//sequential common subsequences
		List<CommonADT<T>> commonSubsequence = new ArrayList<CommonADT<T>>();
		for(int i = m, j = n; i > 0 & j > 0;){				
			int direction = b[i][j];			
			List<T> ss = new ArrayList<T>();
			switch(direction){
			case DIAG: {
				while(b[i][j] == DIAG && i > 0 && j > 0){					
					commonSubsequence.add(0, new CommonADT<T>(left.get(i - 1), i, j));
					ss.add(0, left.get(i - 1));
					i = i-1;
					j = j-1;
				}				
			}break;
			case UP: {
						i-=1;
					 }break;
			case LEFT: {
						j-=1;
						}break;
			}			
		}		
		return commonSubsequence;
	}	
}
