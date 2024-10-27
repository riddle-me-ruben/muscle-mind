from flask import render_template

class QuizRetrievalManager:
    def __init__(self, db_manager):
        self.db_manager = db_manager

    def get_quiz_by_id(self, quiz_id):
        quiz = self.fetch_quiz(quiz_id)
        if not quiz:
            return None
        questions = self.build_questions(quiz)
        return {'title': quiz[0][0], 'questions': questions}

    def fetch_quiz(self, quiz_id):
        """Fetch quiz details and questions from the database."""
        quiz_query, params = self.build_quiz_query(quiz_id)
        quiz = self.db_manager.execute_query(quiz_query, params)
        return quiz

    def build_quiz_query(self, quiz_id):
        """Construct the SQL query for retrieving quiz details."""
        columns = ['title']
        num_questions = 10

        for i in range(num_questions):
            question_idx = i + 1
            columns += [
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2',
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ]

        query = f"SELECT {', '.join(columns)} FROM quizzes WHERE quiz_id = %s"
        return query, (quiz_id,)

    def build_questions(self, quiz):
        """Build the list of questions from the quiz result."""
        num_questions = 10
        questions = []

        for i in range(num_questions):
            question_idx = 1 + i * 6  # Calculate the starting index for each question block
            if quiz[0][question_idx]:
                questions.append({
                    'question': quiz[0][question_idx],
                    'options': [
                        quiz[0][question_idx + 1],
                        quiz[0][question_idx + 2],
                        quiz[0][question_idx + 3],
                        quiz[0][question_idx + 4]
                    ],
                    'correct_option': quiz[0][question_idx + 5]
                })

        return questions

    def quiz_detail(self, quiz_id):
        """Render the quiz detail page."""
        quiz = self.get_quiz_by_id(quiz_id)
        if not quiz:
            return "Quiz not found", 404
        return render_template('quiz-detail.html', quiz=quiz)

    def get_user_quizzes(self, user_email):
        """Retrieve the quizzes created by the user."""
        query = "SELECT quiz_id, title FROM quizzes WHERE user_email = %s"
        return self.db_manager.execute_query(query, (user_email,))
