use etg_evolve::{conserved_sum, DiffuseEvolver, Evolver, Field1D};

#[test]
fn conservation_check_uniform() {
    // Start from a uniform field; zero-flux diffusion should preserve total sum.
    let mut f = Field1D::new(vec![2.0; 128]);
    let mut ev = DiffuseEvolver { alpha: 0.05 };
    let steps = 500;
    let dt = 0.01;

    let mut prev = f.clone();
    for _ in 0..steps {
        ev.step(&mut f, dt);
        assert!(
            conserved_sum(&prev, &f, 1e-12),
            "conservation violated: prev_sum={}, next_sum={}",
            prev.sum(),
            f.sum()
        );
        prev = f.clone();
    }
}

#[test]
fn stability_small_coupling() {
    // Small perturbation about uniform background; ensure bounded and finite.
    let mut data = vec![1.0; 200];
    data[100] += 1e-6;
    data[101] -= 1e-6;
    let mut f = Field1D::new(data);

    let mut ev = DiffuseEvolver { alpha: 0.01 };
    for _ in 0..10_000 {
        ev.step(&mut f, 0.001);
    }
    for &x in &f.data {
        assert!(x.is_finite(), "non-finite value encountered");
        assert!(x.abs() < 10.0, "unbounded growth detected: {x}");
    }
}