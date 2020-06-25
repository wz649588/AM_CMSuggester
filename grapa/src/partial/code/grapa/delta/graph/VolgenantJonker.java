package partial.code.grapa.delta.graph;

public class VolgenantJonker {
	public VolgenantJonker()
    {
        BIG = 100000;
    }

    public double computeAssignment(double costMatrix[][])
    {
        int dim = costMatrix.length;
        rowsol = new int[dim];
        colsol = new int[dim];
        double u[] = new double[dim];
        double v[] = new double[dim];
        return lap(dim, costMatrix, rowsol, colsol, u, v);
        
    }

    public double lap(int dim, double assigncost[][], int rowsol[], int colsol[], double u[], double v[])
    {
        int numfree = 0;
        int j = 0;
        int j1 = 0;
        int j2 = 0;
        int endofpath = 0;
        int last = 0;
        int low = 0;
        int up = 0;
        double min = 0.0D;
        int free[] = new int[dim];
        int collist[] = new int[dim];
        int matches[] = new int[dim];
        double d[] = new double[dim];
        int pred[] = new int[dim];
        for(int i = 0; i < dim; i++)
            matches[i] = 0;

        for(j = dim - 1; j >= 0; j--)
        {
            min = assigncost[0][j];
            int imin = 0;
            for(int i = 1; i < dim; i++)
                if(assigncost[i][j] < min)
                {
                    min = assigncost[i][j];
                    imin = i;
                }

            v[j] = min;
            if(++matches[imin] == 1)
            {
                rowsol[imin] = j;
                colsol[j] = imin;
            } else
            {
                colsol[j] = -1;
            }
        }

        for(int i = 0; i < dim; i++)
        {
            if(matches[i] == 0)
            {
                free[numfree++] = i;
                continue;
            }
            if(matches[i] != 1)
                continue;
            j1 = rowsol[i];
            min = BIG;
            for(j = 0; j < dim; j++)
                if(j != j1 && assigncost[i][j] - v[j] < min)
                    min = assigncost[i][j] - v[j];

            v[j1] = v[j1] - min;
        }

        int loopcnt = 0;
        do
        {
            loopcnt++;
            int k = 0;
            int prvnumfree = numfree;
            numfree = 0;
            do
            {
                if(k >= prvnumfree)
                    break;
                int i = free[k];
                k++;
                double umin = assigncost[i][0] - v[0];
                j1 = 0;
                double usubmin = BIG;
                for(j = 1; j < dim; j++)
                {
                    double h = assigncost[i][j] - v[j];
                    if(h >= usubmin)
                        continue;
                    if(h >= umin)
                    {
                        usubmin = h;
                        j2 = j;
                    } else
                    {
                        usubmin = umin;
                        umin = h;
                        j2 = j1;
                        j1 = j;
                    }
                }

                int i0 = colsol[j1];
                if(umin < usubmin)
                    v[j1] = v[j1] - (usubmin - umin);
                else
                if(i0 >= 0)
                {
                    j1 = j2;
                    i0 = colsol[j2];
                }
                rowsol[i] = j1;
                colsol[j1] = i;
                if(i0 >= 0)
                    if(umin < usubmin && umin - usubmin > 2.8025969286496341E-045D)
                        free[--k] = i0;
                    else
                        free[numfree++] = i0;
            } while(true);
        } while(loopcnt < 2);
        for(int f = 0; f < numfree; f++)
        {
            int freerow = free[f];
            for(j = 0; j < dim; j++)
            {
                d[j] = assigncost[freerow][j] - v[j];
                pred[j] = freerow;
                collist[j] = j;
            }

            low = 0;
            up = 0;
            boolean unassignedfound = false;
            int i;
            do
            {
                if(up == low)
                {
                    last = low - 1;
                    min = d[collist[up++]];
                    int k;
                    for(k = up; k < dim; k++)
                    {
                        j = collist[k];
                        double h = d[j];
                        if(h > min)
                            continue;
                        if(h < min)
                        {
                            up = low;
                            min = h;
                        }
                        collist[k] = collist[up];
                        collist[up++] = j;
                    }

                    k = low;
                    do
                    {
                        if(k >= up)
                            break;
                        if(colsol[collist[k]] < 0)
                        {
                            endofpath = collist[k];
                            unassignedfound = true;
                            break;
                        }
                        k++;
                    } while(true);
                }
                if(!unassignedfound)
                {
                    j1 = collist[low];
                    low++;
                    i = colsol[j1];
                    double h = assigncost[i][j1] - v[j1] - min;
                    for(int k = up; k < dim; k++)
                    {
                        j = collist[k];
                        double v2 = assigncost[i][j] - v[j] - h;
                        if(v2 >= d[j])
                            continue;
                        pred[j] = i;
                        if(v2 == min)
                        {
                            if(colsol[j] < 0)
                            {
                                endofpath = j;
                                unassignedfound = true;
                                break;
                            }
                            collist[k] = collist[up];
                            collist[up++] = j;
                        }
                        d[j] = v2;
                    }

                }
            } while(!unassignedfound);
            for(int k = 0; k <= last; k++)
            {
                j1 = collist[k];
                v[j1] = (v[j1] + d[j1]) - min;
            }

            do
            {
                i = pred[endofpath];
                colsol[endofpath] = i;
                j1 = endofpath;
                endofpath = rowsol[i];
                rowsol[i] = j1;
            } while(i != freerow);
        }

        double lapcost = 0.0D;
        for(int i = 0; i < dim; i++)
        {
            j = rowsol[i];
            u[i] = assigncost[i][j] - v[j];
            lapcost += assigncost[i][j];
        }

        pred = null;
        free = null;
        collist = null;
        matches = null;
        d = null;
        return lapcost;
    }

    public int[] getAssignment()
    {
        return rowsol;
    }

    public int computeAssignment(int matrix[][])
    {
        return 0;
    }

    int BIG;
    int rowsol[];
    int colsol[];
	public int[][] run(double[][] costMatrix) {
		// TODO Auto-generated method stub
		computeAssignment(costMatrix);
		int solution[] = rowsol;
        int[][] assignment = new int[costMatrix.length][2];
        for(int i = 0; i < solution.length; i++)
        {
            assignment[i][0] = i;
            assignment[i][1] = solution[i];
        }
		return assignment;
	}
}
