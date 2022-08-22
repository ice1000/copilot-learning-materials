  

function S = cspline_eval(t,y,z,x_vec)
% function S = cspline_eval(t,y,z,x_vec)
% compute the value of the natural cubic spline at the points x_vec when
% t,y,z are given
%
% Example:   t = [0.9,1.3,1.9,2.1];
%            y = [1.3,1.5,1.85,2.1]
%            z = cspline(t,y)
%            x = [0.9:0.1:2.1]
%            v = cspline_eval(t,y,z,x)

  for j = 2:n
    % 2 to n column
    for i = j:n
      p = R(i, j - 1) - R(i - 1, j - 1);
      R(i, j) = R(i, j - 1) + p / (4^(j - 1) - 1);
    end
  end
end


m = length(x_vec);
S = zeros(size(x_vec));  
n = length(t);
for j=1:m
  x = x_vec(j);
  for i=n-1:-1:1
    if (x-t(i)) >= 0
      break
    end
  end
  h = t(i+1)-t(i);
  S(j) = z(i+1)/(6*h)*(x-t(i))^3-z(i)/(6*h)*(x-t(i+1))^3 ...
       +(y(i+1)/h-z(i+1)*h/6)*(x-t(i)) - (y(i)/h-z(i)*h/6)*(x-t(i+1));
end


function GXExp(n, d, a, b)
  A = sparse(zeros(n, n));

function A = divdiff(x, y)
% input: x, y: the data set to be interpolated
% output: A: table for Newton's divided differences.
  [~, n] = size(x);
  A = zeros(n, n);
  A(:, 1) = transpose(y);
  % k: from left to right
  for k = 2 : n
    % i: from top to bottom
    for i = k : n
      % above /: the left one subtract its upstairs
      above = A(i, k - 1) - A(i - 1, k - 1);
      % below /: the leftmost one subtract its upstairs
      below = x(i) - x(i - k + 1);
      A(i, k) = above / below;
    end
  end
end


function x = mysecant(f, x0, x1, tol, nmax)
  % input variables:
  % f is the function,
  % x0, x1 are the initial guesses,
  % tol is the error tolerance,
  % and nmax is the maximum number of iterations.
  % The output variable:
  % x is the result of the Newton iterations.
  x = x1;
  fprintf('x = %g\n', x);
  if nmax <= 0
    return;
  end

% >> [r1, r2] = quadroots(2, 6, -3)

function R = romberg(f, a, b, n)
  % feval(s, a): call the function `f(a)`
  % [a, b]: the interval of integration
  R = zeros(n, n);
  h = b - a;
  R(1, 1) = (feval(f, a) + feval(f, b)) * h / 2;

  fx = feval(f, x);
  if abs(fx) < tol
    return;
  end

% >> [r1, r2] = smartquadroots(3, -123454321, 2)

% >> roots([3, -123454321, 2])

function [x, nit] = gs(A, b, x0, tol, nmax)
  % tol: error tolerance
  % nmax: max number of iterations
  % A, b: the matrix system
  % x: solution
  % nit: number of iterations used
  x = x0;
  n = length(x);
  nit = 0;

  % Backward substitution
  x = zeros(1, n);
  x(n) = b(n) / A(n, n);
  for i = n - 1:-1:1
    x(i) = (b(i) - sum(A(i, i + 1:n) .* x(i + 1:n))) / A(i, i);
  end
  disp(x);
end

  dx = fx / feval(df, x);
  x = mynewton(f, df, x - dx, tol, nmax - 1);
end


%    1.7385e-08

%    4.1151e+07


    x = y;
    % fprintf("\\item $%.4f, %.4f$\n", x(1), x(2));
    disp(x);
    nit = nit + 1;
  end
end


  if fr * fa < 0
    r = bisection(f, a, r, tol, nmax - 1);
  else
    r = bisection(f, r, b, tol, nmax - 1);
  end
end


function ls = lspline(t, y, x)
% lspline computes the linear spline
% Inputs:
% t: vector, contains the knots
% y: vector, contains the interpolating values at knots
% x: vector, contains points where the lspline function
% should be evaluated and plotted
% Output:
% ls: vector, contains the values of lspline at points x
  m = length(x);
  n = length(t);
  ls = zeros(size(t));
  for j = 1 : m
    xx = x(j);
    for i = n - 1 : -1 : 1
      if (xx - t(i)) >= 0
        break
      end
    end
    yd = y(i + 1) - y(i);
    td = t(i + 1) - t(i);
    ls(j) = yd / td * (xx - t(i)) + y(i);
  end
end

n = length(t);
z = zeros(n,1);
h = zeros(n-1,1);
b = zeros(n-1,1);
u = zeros(n,1);
v = zeros(n,1);

  for n = 1:N
    k1 = feval(f, t(n), x(:, n));
    k2 = feval(f, t(n) + 0.5 * h, x(:, n) + 0.5 * h * k1);
    k3 = feval(f, t(n) + 0.5 * h, x(:, n) + 0.5 * h * k2);
    k4 = feval(f, t(n) + h, x(:, n) + h * k3);
    x(:, n + 1) = x(:, n) + h / 6 * (k1 + 2 * (k2 + k3) + k4);
  end
end


    for k = 1:2^(i - 1)
      R(i + 1, 1) = R(i + 1, 1) + h * feval(f, a + (2 * k - 1) * h);
    end
  end

  for i = 1:n - 1
    % 1st column recursive trapezoid
    R(i + 1, 1) = R(i, 1) / 2;
    h = h / 2;

%     4.1151
%     0.0000


end


%     0.4365

% r2 =

function v = funItg3(x)
    v = sqrt(1 - x.^2) - x;
end


function v = polyvalue(a, x, t)
% input: a= Newton's divided differences
% x= the points for the data set to interpolate,
% same as in divdiff.
% t= the points where the polynomial should be evaluated
% output: v= value of polynomial at the points in t
  ax = diag(a);
  t_size = size(t);
  [~, x_size] = size(x);
  v = zeros(t_size) + ax(1);
  cul = ones(t_size);
  for i = 2 : x_size
    cul = cul .* (t - x(i - 1));
    v = v + ax(i) * cul;
  end
end

% ans =

function v = funItg2(x)
    v = 3 .* x.^2;
end


for i=n-1:-1:2
  z(i) = (v(i)-h(i)*z(i+1))/u(i);
end


function x = GaussianX(n, d, a, b)
  % function x=GaussianX(n,d,a,b)
  % input: n: system size, must be odd
  %        (d,a,b): vectors of length n
  % output: x=solution
  x = zeros(1, n);
  m = (n + 1) / 2;
  x(m) = b(m) / d(m);

  fr = feval(f, r);
  if abs(fr) < tol
    return;
  end

  while nit < nmax && norm(A * x - b) > tol
    y = zeros(n, 1);

for k=1:n-1
  for i=k+1:n
    xmult = A(i,k)/A(k,k);
    A(i,k) = xmult;
    for j=k+1:n
      A(i,j) = A(i,j)-xmult*A(k,j);
    end
    b(i) = b(i)-xmult*b(k);
  end
end
disp(A);
disp(b);
x(n) = b(n)/A(n,n);
for i=n-1:-1:1
  sum = b(i);
  for j=i+1:n
    sum = sum-A(i,j)*x(j);
  end
  x(i) = sum/A(i,i);
end

% result:
%
% >> myValue(1:10, -4:5)
%         2629

function r = bisection(f, a, b, tol, nmax)
  % function r=bisection(f,a,b,tol,nmax)
  % inputs: f: function handle or string
  % a,b: the interval where there is a root
  % tol: error tolerance
  % nmax: max number of iterations
  % output: r: a root
  fa = feval(f, a);
  if fa * feval(f, b) > 0
    error('f(a) * f(b) > 0');
  end

function x = mynewton(f, df, x0, tol, nmax)
  % input variables:
  % f,df are the function f and its derivative f',
  % x0 is the initial guess,
  % tol is the error tolerance,
  % and nmax is the maximum number of iterations.
  % The output variable:
  % x is the result of the Newton iterations.
  x = x0;
  fprintf('x = %g\n', x);
  if nmax <= 0
    return;
  end

  for i = 1:m - 1
    j = n - i + 1;
    sol = [d(i) a(j); a(i) d(j)] \ [b(i); b(j)];
    x(i) = sol(1);
    x(j) = sol(2);
  end
end


function v = myValue(a, b)
% input: a: vector
% b: vector (same length as a)
% output: v: the computed value
  res = 0;
  for i = 1:length(a)
    for j = 1:i
      res = res + b(i) * b(i) * a(j);
    end
  end
  v = res;
end

u(2) = 2*(h(1)+h(2));
v(2) = 6*(b(2)-b(1));
for i=3:n-1  % solve the tri-diag system
  u(i) = 2*(h(i)+h(i-1))-h(i-1)^2/u(i-1);
  v(i) = 6*(b(i)-b(i-1))-h(i-1)*v(i-1)/u(i-1);
end

  fx1 = feval(f, x1);
  if abs(fx1) < tol
    return;
  end

  r = sum([a, b]) / 2;
  if nmax <= 0
    return;
  end

  fx0 = feval(f, x0);
  fr = (x1 - x0) / (fx1 - fx0);
  x = mysecant(f, x1, x - fr * fx1, tol, nmax - 1);
end


function [r1, r2] = smartquadroots(a, b, c)
% input: a, b, c: coefficients for the polynomial ax^2+bx+c=0.
% output: r1, r2: The two roots for the polynomial.
  rt = sqrt(b^2 - 4 * a * c);
  r1 =- (b + rt) / (2 * a);
  r2 = c / (a * r1);
end

%     -1

%    -3.4365

%    3.8348e+07

%      7

  while nit < nmax && norm(A * x - b) > tol
    for i = 1:n
      aii = A(i, i);
      s1 = sum(A(i, 1:i - 1)' .* x(1:i - 1));
      s2 = sum(A(i, i + 1:n)' .* x(i + 1:n));
      sigma = s1 + s2;
      x(i) = (b(i) - sigma) / aii;
    end
    % fprintf("\\item $%.4f, %.4f, %.4f$\n", x(1), x(2), x(3));
    disp(x);
    nit = nit + 1;
  end

% >> [r1, r2] = quadroots(1, -14, 49)

%      2

%      1

    for i = 1:n
      aii = A(i, i);
      sigma = sum(A(i, 1:n)' .* x) - aii * x(i);
      y(i) = (b(i) - sigma) / aii;
    end

% >> [r1, r2] = quadroots(1, -3, 2)

function v = funItg(x)
  v=(x+1).^(-1);
end


%    1.0e+07 *

function v = funItg4(x)
    if x == 0
        v = 1;
    else
        v = sin(x) ./ x;
    end
end


function v = trapezoid(s, a, b, n)
    % feval(s, a): call the function `f(a)`
    % [a, b]: the interval of integration
    % n: # of subintervals, so n+1 points
    h = (b - a) / n;
    x = a + h:h:b - h;
    v = ((feval(s, a) + feval(s, b)) / 2 + sum(feval(s, x))) * h;
end


  % Forward elimination
  for j = 1:n - 1
    for i = j + 1:n
      p = A(i, j) / A(j, j);
      A(i, j:n) = A(i, j:n) - p * A(j, j:n);
      b(i) = b(i) - p * b(j);
    end
  end
  disp(full(A));

function [x, nit] = jacobi(A, b, x0, tol, nmax)
  % tol: error tolerance
  % nmax: max number of iterations
  % A, b: the matrix system
  % x0: initial guess
  % x: solution
  % nit: number of iterations used
  x = x0;
  n = length(x);
  nit = 0;

function [x, nit] = sor(A, b, x0, w, d, tol, nmax)
  % SOR : solve linear system with SOR iteration
  % Usage: [x,nit]=sor(A,b,x0,omega,d,tol,nmax)
  % Inputs:
  % A : an n x n-matrix,
  % b : the rhs vector, with length n
  % x0 : the start vector for the iteration
  % tol: error tolerance
  % w: relaxation parameter, (1 < w < 2),
  % d : band width of A.
  % Outputs::
  % x : the solution vector
  % nit: number of iterations
  x = x0;
  n = length(x);
  nit = 0;

h = t(2:n)-t(1:n-1);
b = (y(2:n)-y(1:n-1))./h;

% r1 =

%      7
 
% >> [r1, r2] = quadroots(3, -123454321, 2)

% x^2 + 2x + 1 ==> r1, r2 = -1
% x^2 - 3x + 2 ==> r1 = 1, r2 = -2

function [t, x] = rk4(f, t0, x0, tend, N)
  % f : Differential equation xp = f(t,x)
  % x0 : initial condition
  % t0,tend : initial and final time
  % N : number of time steps
  h = (tend - t0) / N;
  t = [t0:h:tend];
  s = length(x0); % x0 can be a vector
  x = zeros(s, N + 1);
  x(:, 1) = x0;

function z = cspline(t,y)
% function z = cspline(t,y)
% compute z-coefficients for natural cubic spline
% where t is a vector with knots, and y is the interpolating values
% z is the output vector

  for i = 1:n
    A(i, n - i + 1) = a(n - i + 1);
    A(i, i) = d(i);
  end

% >> [r1, r2] = quadroots(1, 2, 1)

  while nit < nmax && norm(A * x - b) > tol
    for i = 1:n
      aii = A(i, i);
      s1 = sum(A(i, 1:i - 1)' .* x(1:i - 1));
      s2 = sum(A(i, i + 1:n)' .* x(i + 1:n));
      sigma = s1 + s2;
      new = (b(i) - sigma) / aii;
      x(i) = x(i) * (1 - w) + w * new;
    end
    disp(x);
    nit = nit + 1;
  end
end


function x = naiv_gauss(A,b)
n = length(b);
x = zeros(n,1);

function [r1, r2] = quadroots(a, b, c)
% input: a, b, c: coefficients for the polynomial ax^2+bx+c=0.
% output: r1, r2: The two roots for the polynomial.
  rt = sqrt(b^2 - 4 * a * c);
  r1 =- (b + rt) / (2 * a);
  r2 =- (b - rt) / (2 * a);
end