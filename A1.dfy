method SquareRoot(n:int) returns (r:int)
  requires n >= 0
  ensures r >= 0 && r*r <= n < (r+1)*(r+1)
{
  // The method is partially correct. 
  // Justification: WP := n >= 0;
  //The requires n>= 0 <==> wp
  ghost var WP: bool;
  ghost var WP_s: bool;
  WP := n >= 0; //arithmetic
  WP := true && 0 <= n && true;
  WP := 0 >= 0 && 0*0 <= n < (n+1) * (n+1) && n+1 >= 0+1;
  r := 0;
  WP := r >= 0 && r*r <= n < (n+1) * (n+1) && n+1 >= r+1;
  var y, h := n+1, 0;
  WP := r >= 0 && r*r <= n < y*y && y >= r+1; //{J}
  
  while (y != r+1)
    invariant r >= 0 && r*r <= n < y*y && y >= r+1
  {
     WP_s:= y > r+1; // {B && J}
     //strengthen with y != r+1 {B}
     WP := y >= r+1; // Q2a {J}
    // WP := P ==> Q && !P ==> Q ==Q 
    // mark P with {((r+y)/2)*((r+y)/2) <= n}  Q with y >= r+1
    WP := ((r+y)/2)*((r+y)/2) <= n ==> y >= r+1 && (n < ((r+y)/2)*((r+y)/2) ==> y >= r + 1);
    // (Q2c)(a+b)/2 >= a + 1 = b >= a + 1, when (a+b)/2*((a+b)/2) > a*a
    // when (y+r)/2*((y+r)/2) > r * r;
    // need to satisfy y > r
    // because invariant y >= r+1, so y > r. so the condition of (a+b)/2*((a+b)/2) > a*a hold
    WP := (((r+y)/2)*((r+y)/2) <= n ==> y >= r+1) && (n < ((r+y)/2)*((r+y)/2) ==> ((r+y)/2) >= r+1);
    //Q2b b >= (a+b)/2 + 1 = b >= a + 1
    WP := (((r+y)/2)*((r+y)/2) <= n ==> y >= ((r+y)/2)+1) && (n < ((r+y)/2)*((r+y)/2) ==> ((r+y)/2) >= r+1);
    h := (r+y)/2;
    WP := (h*h <= n ==> y >= h+1) && (n < h*h ==> h >=r+1); // invariant n < y*y
    WP := (h*h <= n ==> n < y*y && y >= h+1) && (n < h*h ==> h >= r+1); 
    // r >=0 && y >= r + 1 >=0 so (r+y)/2 >=0 == h>=0
    WP := (h*h <= n ==> h >= 0 && n < y*y && y >= h+1) && (n <= h*h ==> h >= r+1);
     WP := (h*h <= n ==> h >= 0 && h*h <= n < y*y && y >= h+1) &&
     (h*h > n ==> r >= 0 && r*r <= n < h*h && h >= r+1);

        WP := (h*h <= n ==> h >= 0 && h*h <= n < y*y && y >= h+1) &&
          (h*h > n ==> r >= 0 && r*r <= n < h*h && h >= r+1);
    if h*h <= n {
      WP := h >= 0 && n < y*y && y >= h+1; //if h*h <= n
      WP := h >= 0 && h*h <= n < y*y && y >= h+1;
      r := h;
      WP := r >= 0 && r*r <= n < y*y && y >= r+1;//{J}
    } else {
      WP := h >= r+1; // because of invariant, so r >= 0 && r*r <= n is true
      WP := r >= 0 && r*r <= n && h >= r+1; //  n < h*h is true
      WP := r >= 0 && r*r <= n < h*h && h >= r+1;
      y := h;
      WP := r >= 0 && r*r <= n < y*y && y >= r+1; //{J}
    }
  }
  WP_s:= r >= 0 && r*r <= n < y*y && y >= r+1;  //invariant && negation of guard
  //strengthen with  y >= r+1 && n < y*y
  //because y >=r+1 so y*y >= (r+1)*(r+1)
  WP := r >= 0 && r*r <= n < (r+1)*(r+1); //postcondition
}

/* Use of generative Artificial Intelligence (AI):
1. translate the questions and instructions and warnings of the code
2. use the AI to check the result of my code.
*/