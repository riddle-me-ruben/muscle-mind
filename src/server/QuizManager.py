class QuizManager:
    def __init__(self, db_manager, session):
        from QuizCreationManager import QuizCreationManager
        from QuizRetrievalManager import QuizRetrievalManager
        from QuizSubmissionManager import QuizSubmissionManager

        self.quiz_creation = QuizCreationManager(db_manager)
        self.quiz_retrieval = QuizRetrievalManager(db_manager)
        self.quiz_submission = QuizSubmissionManager(db_manager, self.quiz_retrieval)

    def create_quiz(self):
        return self.quiz_creation.create_quiz()

    def submit_quiz(self):
        return self.quiz_creation.submit_quiz()

    def get_user_quizzes(self, user_email):
        return self.quiz_retrieval.get_user_quizzes(user_email)

    def quiz_detail(self, quiz_id):
        return self.quiz_retrieval.quiz_detail(quiz_id)

    def take_quiz(self, quiz_id, question_num):
        return self.quiz_submission.take_quiz(quiz_id, question_num)

    def submit_quiz_answer(self, quiz_id, question_num):
        return self.quiz_submission.submit_quiz_answer(quiz_id, question_num)

    def score(self, quiz_id, score, total):
        return self.quiz_submission.score(quiz_id, score, total)

    def penalty(self, quiz_id, question_num):
        return self.quiz_submission.penalty(quiz_id, question_num)
