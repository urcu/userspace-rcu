echo testing no ipi
make urcu_free | tee urcu_free.log
echo testing no ipi
make urcu_free_no_mb | tee urcu_free_no_mb.log
echo testing no ipi
make urcu_free_no_rmb | tee urcu_free_no_rmb.log
echo testing no ipi
make urcu_free_no_wmb | tee urcu_free_no_wmb.log
echo testing no ipi
make urcu_free_single_flip | tee urcu_free_single_flip.log
echo testing no ipi
make urcu_progress_writer | tee urcu_progress_writer.log
echo testing no ipi
make urcu_progress_reader | tee urcu_progress_reader.log
echo testing no ipi
make urcu_progress_writer_error | tee urcu_progress_writer_error.log
echo testing no ipi
make asserts | tee asserts.log
